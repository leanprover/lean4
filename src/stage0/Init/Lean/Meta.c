// Lean compiler output
// Module: Init.Lean.Meta
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.LOption Init.Lean.Trace Init.Lean.AuxRecursor Init.Lean.Class Init.Lean.WHNF Init.Lean.ReducibilityAttrs
#include "runtime/lean.h"
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
uint8_t l_Lean_isReducible(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_18__isAuxDef_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_3__getEnv(lean_object*);
lean_object* l___private_Init_Lean_Meta_32__inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl(lean_object*);
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2;
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_sort(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_11__getOptions___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_30__inferProjType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_3__getEnv___rarg(lean_object*);
size_t lean_expr_hash(lean_object*);
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_9__reduceReducibleOnly_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_15__assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shift__right(size_t, size_t);
lean_object* l___private_Init_Lean_Meta_36__checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_smartUnfoldingSuffix;
lean_object* l___private_Init_Lean_Meta_7__mkFreshId(lean_object*);
lean_object* l___private_Init_Lean_Meta_8__reduceAll_x3f(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_Hashable___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_26__isClassExpensive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_2__getMCtx___rarg(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_mvar(lean_object*);
lean_object* l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_26__isClassExpensive___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_4__throwEx(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_Inhabited;
size_t l_USize_sub(size_t, size_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_6__whenDebugging(lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Init_Lean_Meta_28__inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_3__toCtorIfLit(lean_object*);
lean_object* l___private_Init_Lean_Meta_22__whnfAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_WHNF_6__isIdRhsApp(lean_object*);
lean_object* l___private_Init_Lean_WHNF_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_13__isExprAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_15__assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_10__getTransparency(lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_tracer___closed__2;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__1;
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_7__extractIdRhs(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_10__getTransparency___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_25__isClassQuick(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_30__inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_11__getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReducible___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux(lean_object*);
lean_object* l_Lean_Meta_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_35__inferFVarType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_1__getLCtx(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_inhabited;
extern lean_object* l_unreachable_x21___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_26__isClassExpensive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_21__cacheWHNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_23__withCacheScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_5__throwBug___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_22__whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_4__throwEx___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuickConst(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_8__reduceAll_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_31__getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_29__inferConstType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_16__getTraceState___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_13__isExprAssigned(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_7__mkFreshId___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_29__inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l___private_Init_Lean_Meta_7__mkFreshId___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
extern lean_object* l_unreachable_x21___rarg___closed__2;
lean_object* l___private_Init_Lean_Meta_9__reduceReducibleOnly_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer;
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_imax(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l___private_Init_Lean_Meta_17__getConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_inhabited;
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_2__getMCtx(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_27__getForallResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1;
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* lean_level_mk_succ(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_2__getMCtx___boxed(lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Meta_tracer___closed__1;
lean_object* l_Lean_Meta_forallTelescope(lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_23__withCacheScope(lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_3__getEnv___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_1__getLCtx___boxed(lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_valueOpt(lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l___private_Init_Lean_Meta_32__inferForallType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__2;
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_5__throwBug___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_18__isAuxDef_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_16__getTraceState___rarg(lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___closed__4;
lean_object* l___private_Init_Lean_Meta_5__throwBug(lean_object*);
lean_object* l___private_Init_Lean_Meta_20__getCachedWHNF___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_Hashable___closed__1;
extern lean_object* l_Lean_Expr_inhabited___closed__1;
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_34__inferMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
extern lean_object* l_Lean_Expr_HasBeq;
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_6__whenDebugging___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_auxRecExt;
uint8_t lean_expr_has_expr_mvar(lean_object*);
extern lean_object* l_Lean_Expr_Hashable;
lean_object* l_Prod_HasBeq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___closed__3;
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_14__getMVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_17__getConst(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Meta_isClassQuickConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_HasBeq;
lean_object* l_Lean_Meta_TransparencyMode_Hashable;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1;
lean_object* l_Lean_Meta_Exception_inhabited___closed__1;
lean_object* l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_4__throwEx___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_19__getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1;
lean_object* l_Lean_Meta_isReducible(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_16__getTraceState(lean_object*);
lean_object* l___private_Init_Lean_Meta_28__inferAppType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_34__inferMVarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1;
lean_object* l___private_Init_Lean_Meta_21__cacheWHNF(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_14__getMVarAssignment(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_20__getCachedWHNF(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t _init_l_Lean_Meta_TransparencyMode_Inhabited() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
return x_1;
}
}
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
size_t x_2; 
x_2 = 7;
return x_2;
}
case 1:
{
size_t x_3; 
x_3 = 11;
return x_3;
}
default: 
{
size_t x_4; 
x_4 = 13;
return x_4;
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_Hashable___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Exception_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Exception_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MetaM_inhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_1__getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_1__getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_1__getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_2__getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_2__getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_2__getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_2__getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_2__getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_3__getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_3__getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_3__getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_3__getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_3__getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_4__throwEx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_4__throwEx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_4__throwEx___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_4__throwEx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_4__throwEx___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_5__throwBug___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_5__throwBug(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_5__throwBug___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_5__throwBug___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_5__throwBug___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_6__whenDebugging___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_6__whenDebugging(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_6__whenDebugging___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_7__mkFreshId___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_name_mk_numeral(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 3, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_18);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_26 = x_18;
} else {
 lean_dec_ref(x_18);
 x_26 = lean_box(0);
}
lean_inc(x_25);
lean_inc(x_24);
x_27 = lean_name_mk_numeral(x_24, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_25, x_28);
lean_dec(x_25);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
lean_object* l___private_Init_Lean_Meta_7__mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_7__mkFreshId___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_7__mkFreshId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_7__mkFreshId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_8__reduceAll_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = 0;
x_6 = l_Lean_Meta_TransparencyMode_beq(x_4, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_8__reduceAll_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_8__reduceAll_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_9__reduceReducibleOnly_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = 2;
x_6 = l_Lean_Meta_TransparencyMode_beq(x_4, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_9__reduceReducibleOnly_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_9__reduceReducibleOnly_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_10__getTransparency(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_10__getTransparency___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_10__getTransparency(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_11__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_11__getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_11__getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_isReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_isReducible(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_isReducible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isReducible(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_find_decl(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_5);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_13__isExprAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_metavar_ctx_is_expr_assigned(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_13__isExprAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_13__isExprAssigned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_14__getMVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_metavar_ctx_get_expr_assignment(x_4, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_14__getMVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_14__getMVarAssignment(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_15__assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_metavar_ctx_assign_expr(x_8, x_1, x_2);
lean_ctor_set(x_4, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_18 = lean_metavar_ctx_assign_expr(x_13, x_1, x_2);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
lean_inc(x_1);
lean_inc(x_23);
x_28 = lean_metavar_ctx_is_expr_assigned(x_23, x_1);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_4, 5);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 4);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 3);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 0);
lean_dec(x_35);
x_36 = lean_metavar_ctx_assign_expr(x_23, x_1, x_2);
lean_ctor_set(x_4, 1, x_36);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_39 = lean_metavar_ctx_assign_expr(x_23, x_1, x_2);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_24);
lean_ctor_set(x_40, 3, x_25);
lean_ctor_set(x_40, 4, x_26);
lean_ctor_set(x_40, 5, x_27);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_23);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_15__assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_15__assignExprMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_16__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_16__getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_16__getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_16__getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_16__getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 4);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 4, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_13);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_11__getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_16__getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_tracer___closed__1;
x_2 = l_Lean_Meta_tracer___closed__2;
x_3 = l_Lean_Meta_tracer___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tracer___closed__4;
return x_1;
}
}
lean_object* l_Lean_Meta_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_17__getConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_4);
x_6 = lean_environment_find(x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 4);
x_14 = 0;
x_15 = l_Lean_Meta_TransparencyMode_beq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 4);
x_21 = 2;
x_22 = l_Lean_Meta_TransparencyMode_beq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = l_Lean_isReducible(x_4, x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_17__getConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_17__getConst(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_18__isAuxDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_auxRecExt;
x_6 = l_Lean_TagDeclarationExtension_isTagged(x_5, x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_noConfusionExt;
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_4, x_1);
lean_dec(x_4);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Meta_18__isAuxDef_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_18__isAuxDef_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_19__getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_5 = lean_local_ctx_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_unbox(x_10);
lean_dec(x_10);
x_15 = lean_unbox(x_12);
lean_dec(x_12);
x_16 = l_Lean_Meta_TransparencyMode_beq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = lean_expr_eqv(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_24 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_unbox(x_13);
lean_dec(x_13);
x_18 = lean_unbox(x_15);
lean_dec(x_15);
x_19 = l_Lean_Meta_TransparencyMode_beq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_expr_eqv(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
}
}
case 1:
{
lean_object* x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = x_2 >> x_5;
x_26 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2(x_24, x_25, x_3);
lean_dec(x_24);
return x_26;
}
default: 
{
lean_object* x_27; 
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3(x_28, x_29, lean_box(0), x_30, x_3);
return x_31;
}
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_TransparencyMode_hash(x_6);
x_8 = lean_expr_hash(x_5);
lean_dec(x_5);
x_9 = lean_usize_mix_hash(x_7, x_8);
x_10 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2(x_3, x_9, x_2);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_20__getCachedWHNF(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__2(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_20__getCachedWHNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_20__getCachedWHNF(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unbox(x_18);
lean_dec(x_18);
x_23 = lean_unbox(x_20);
lean_dec(x_20);
x_24 = l_Lean_Meta_TransparencyMode_beq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = lean_expr_eqv(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_2 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_array_fset(x_5, x_2, x_3);
x_36 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_37 = lean_array_fset(x_5, x_2, x_3);
x_38 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = x_1 - x_11;
x_13 = 5;
x_14 = x_13 * x_12;
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lean_Meta_TransparencyMode_hash(x_19);
x_21 = lean_expr_hash(x_18);
lean_dec(x_18);
x_22 = lean_usize_mix_hash(x_20, x_21);
x_23 = x_22 >> x_14;
x_24 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_6, x_23, x_1, x_9, x_10);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_unbox(x_21);
lean_dec(x_21);
x_26 = lean_unbox(x_23);
lean_dec(x_23);
x_27 = l_Lean_Meta_TransparencyMode_beq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_15);
x_28 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_fset(x_17, x_12, x_29);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
uint8_t x_31; 
x_31 = lean_expr_eqv(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_15);
x_32 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_array_fset(x_17, x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_35 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
x_42 = lean_unbox(x_38);
lean_dec(x_38);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = l_Lean_Meta_TransparencyMode_beq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_39);
x_45 = l_PersistentHashMap_mkCollisionNode___rarg(x_36, x_37, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
uint8_t x_48; 
x_48 = lean_expr_eqv(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_PersistentHashMap_mkCollisionNode___rarg(x_36, x_37, x_4, x_5);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_array_fset(x_17, x_12, x_50);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_37);
lean_dec(x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_5);
x_53 = lean_array_fset(x_17, x_12, x_52);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
}
}
}
case 1:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = x_2 >> x_9;
x_57 = x_3 + x_8;
x_58 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_55, x_56, x_57, x_4, x_5);
lean_ctor_set(x_15, 0, x_58);
x_59 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_59);
return x_1;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = x_2 >> x_9;
x_62 = x_3 + x_8;
x_63 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_60, x_61, x_62, x_4, x_5);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_array_fset(x_17, x_12, x_64);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
}
default: 
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_5);
x_67 = lean_array_fset(x_17, x_12, x_66);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_67);
return x_1;
}
}
}
}
else
{
lean_object* x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = 1;
x_70 = 5;
x_71 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_72 = x_2 & x_71;
x_73 = lean_usize_to_nat(x_72);
x_74 = lean_array_get_size(x_68);
x_75 = lean_nat_dec_lt(x_73, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_68);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_array_fget(x_68, x_73);
x_78 = lean_box(2);
x_79 = lean_array_fset(x_68, x_73, x_78);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
x_87 = lean_unbox(x_83);
lean_dec(x_83);
x_88 = lean_unbox(x_85);
lean_dec(x_85);
x_89 = l_Lean_Meta_TransparencyMode_beq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_82);
x_90 = l_PersistentHashMap_mkCollisionNode___rarg(x_80, x_81, x_4, x_5);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_array_fset(x_79, x_73, x_91);
lean_dec(x_73);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_expr_eqv(x_84, x_86);
lean_dec(x_86);
lean_dec(x_84);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_95 = l_PersistentHashMap_mkCollisionNode___rarg(x_80, x_81, x_4, x_5);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_array_fset(x_79, x_73, x_96);
lean_dec(x_73);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_81);
lean_dec(x_80);
if (lean_is_scalar(x_82)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_82;
}
lean_ctor_set(x_99, 0, x_4);
lean_ctor_set(x_99, 1, x_5);
x_100 = lean_array_fset(x_79, x_73, x_99);
lean_dec(x_73);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
case 1:
{
lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_77, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
x_104 = x_2 >> x_70;
x_105 = x_3 + x_69;
x_106 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_102, x_104, x_105, x_4, x_5);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_array_fset(x_79, x_73, x_107);
lean_dec(x_73);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
default: 
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_5);
x_111 = lean_array_fset(x_79, x_73, x_110);
lean_dec(x_73);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; size_t x_115; uint8_t x_116; 
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__3(x_1, x_113, x_4, x_5);
x_115 = 7;
x_116 = x_115 <= x_3;
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_114);
x_118 = lean_unsigned_to_nat(4u);
x_119 = lean_nat_dec_lt(x_117, x_118);
lean_dec(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_dec(x_114);
x_122 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_123 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4(x_3, x_120, x_121, x_120, x_113, x_122);
lean_dec(x_121);
lean_dec(x_120);
return x_123;
}
else
{
return x_114;
}
}
else
{
return x_114;
}
}
}
}
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_TransparencyMode_HasBeq;
x_2 = l_Lean_Expr_HasBeq;
x_3 = lean_alloc_closure((void*)(l_Prod_HasBeq___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_TransparencyMode_Hashable;
x_2 = l_Lean_Expr_Hashable;
x_3 = lean_alloc_closure((void*)(l_Prod_Hashable___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 1;
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_unbox(x_10);
lean_dec(x_10);
x_13 = l_Lean_Meta_TransparencyMode_hash(x_12);
x_14 = lean_expr_hash(x_11);
lean_dec(x_11);
x_15 = lean_usize_mix_hash(x_13, x_14);
x_16 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_5, x_15, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = 1;
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_25 = l_Lean_Meta_TransparencyMode_hash(x_24);
x_26 = lean_expr_hash(x_23);
lean_dec(x_23);
x_27 = lean_usize_mix_hash(x_25, x_26);
x_28 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_17, x_27, x_19, x_2, x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
}
lean_object* l___private_Init_Lean_Meta_21__cacheWHNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 4);
x_9 = lean_ctor_get(x_4, 2);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_11, x_13, x_2);
lean_ctor_set(x_5, 0, x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_box(x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_17, x_20, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_4, 2, x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*1 + 4);
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 3);
x_30 = lean_ctor_get(x_4, 4);
x_31 = lean_ctor_get(x_4, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_34 = x_5;
} else {
 lean_dec_ref(x_5);
 x_34 = lean_box(0);
}
x_35 = lean_box(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_1);
x_37 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_32, x_36, x_2);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_29);
lean_ctor_set(x_39, 4, x_30);
lean_ctor_set(x_39, 5, x_31);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_21__cacheWHNF___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_21__cacheWHNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_21__cacheWHNF(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_has_expr_mvar(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_expr_has_level_mvar(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_MetavarContext_instantiateMVars(x_8, x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = l_Lean_MetavarContext_instantiateMVars(x_14, x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 1);
x_26 = l_Lean_MetavarContext_instantiateMVars(x_25, x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_3, 1, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_36 = l_Lean_MetavarContext_instantiateMVars(x_31, x_1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1;
x_2 = l_Lean_Expr_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_panicWithPos___rarg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_panicWithPos___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_panicWithPos___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_panicWithPos___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_4);
x_20 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l_Lean_ConstantInfo_lparams(x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthAux___main___rarg(x_12, x_13);
lean_dec(x_12);
x_15 = l_List_lengthAux___main___rarg(x_8, x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_expr_eqv(x_5, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_21 = lean_instantiate_value_lparams(x_7, x_8);
x_22 = l_Lean_Expr_betaRev(x_21, x_9);
lean_dec(x_21);
x_23 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_22);
x_24 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_23, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_115; lean_object* x_116; 
x_115 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_116 = lean_box(x_115);
switch (lean_obj_tag(x_116)) {
case 2:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_unsigned_to_nat(5u);
x_118 = lean_unsigned_to_nat(3u);
x_12 = x_117;
x_13 = x_118;
goto block_114;
}
case 3:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_unsigned_to_nat(4u);
x_120 = lean_unsigned_to_nat(3u);
x_12 = x_119;
x_13 = x_120;
goto block_114;
}
default: 
{
uint8_t x_121; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_expr_eqv(x_5, x_6);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_11);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_4);
lean_ctor_set(x_124, 1, x_11);
return x_124;
}
}
}
block_114:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_9);
x_15 = lean_nat_dec_lt(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_expr_eqv(x_5, x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_9, x_12);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_20, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Init_Lean_Meta_17__getConst(x_28, x_10, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_5, x_6);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_expr_eqv(x_5, x_6);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
x_43 = lean_box(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_4);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l_Lean_Expr_inhabited;
x_46 = lean_array_get(x_45, x_9, x_13);
x_47 = lean_expr_mk_app(x_46, x_27);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_12, x_48);
x_50 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_14, x_9, x_49, x_47);
lean_dec(x_14);
x_51 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_50, x_10, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_29, 0);
lean_dec(x_53);
x_54 = lean_expr_eqv(x_5, x_6);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_55);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_expr_eqv(x_5, x_6);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_29);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_29, 0);
lean_dec(x_62);
x_63 = lean_expr_eqv(x_5, x_6);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_64);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_expr_eqv(x_5, x_6);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
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
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_21);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_21, 0);
lean_dec(x_75);
x_76 = lean_expr_eqv(x_5, x_6);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_77);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
lean_dec(x_21);
x_79 = lean_expr_eqv(x_5, x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_21);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_21, 0);
lean_dec(x_84);
x_85 = lean_expr_eqv(x_5, x_6);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_86);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_21, 1);
lean_inc(x_87);
lean_dec(x_21);
x_88 = lean_expr_eqv(x_5, x_6);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_4);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_21);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_21, 0);
lean_dec(x_93);
x_94 = lean_expr_eqv(x_5, x_6);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_95);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_dec(x_21);
x_97 = lean_expr_eqv(x_5, x_6);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_4);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_21);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_21, 0);
lean_dec(x_102);
x_103 = lean_expr_eqv(x_5, x_6);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_104);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_21, 1);
lean_inc(x_105);
lean_dec(x_21);
x_106 = lean_expr_eqv(x_5, x_6);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_4);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_21);
if (x_110 == 0)
{
return x_21;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_21, 0);
x_112 = lean_ctor_get(x_21, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_21);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_free_object(x_6);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_25);
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_6);
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_5, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
lean_dec(x_6);
if (lean_obj_tag(x_35) == 5)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 4);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_39 = x_5;
} else {
 lean_dec_ref(x_5);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_43 = x_5;
} else {
 lean_dec_ref(x_5);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_48 = x_5;
} else {
 lean_dec_ref(x_5);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_5, 0);
x_53 = lean_ctor_get(x_5, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_5);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__8(x_1, x_7, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
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
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_expr_mk_const(x_20, x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_22);
x_24 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_25, x_27);
x_29 = l_Array_shrink___main___rarg(x_28, x_3);
x_30 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_29, x_29, x_22, x_21);
lean_dec(x_29);
lean_ctor_set(x_10, 0, x_30);
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_expr_mk_const(x_31, x_8);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_33);
x_35 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_36, x_38);
x_40 = l_Array_shrink___main___rarg(x_39, x_3);
x_41 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_40, x_40, x_33, x_32);
lean_dec(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_45 = x_10;
} else {
 lean_dec_ref(x_10);
 x_45 = lean_box(0);
}
x_46 = lean_expr_mk_const(x_44, x_8);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_47);
x_49 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_48);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_53 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_50, x_52);
x_54 = l_Array_shrink___main___rarg(x_53, x_3);
x_55 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_54, x_54, x_47, x_46);
lean_dec(x_54);
if (lean_is_scalar(x_45)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_45;
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_43);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
return x_63;
}
}
}
lean_object* _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_17__getConst___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn___main(x_13);
x_16 = l_Lean_RecursorVal_getInduct(x_4);
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
uint8_t x_19; 
x_19 = lean_expr_has_expr_mvar(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_11);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_22 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_21, x_13, x_20, x_6, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_6);
lean_inc(x_30);
x_31 = lean_apply_3(x_1, x_30, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_4(x_2, x_13, x_32, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_23);
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_23);
lean_dec(x_30);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
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
lean_free_object(x_23);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
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
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_55);
x_56 = lean_apply_3(x_1, x_55, x_6, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_apply_4(x_2, x_13, x_57, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
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
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_55);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_22);
if (x_78 == 0)
{
return x_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_22, 0);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_22);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_82);
x_84 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
lean_inc(x_13);
x_88 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_13, x_85, x_87);
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
lean_dec(x_4);
lean_inc(x_89);
x_90 = l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_free_object(x_11);
x_91 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_92 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_91, x_13, x_89, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_dec(x_92);
x_99 = !lean_is_exclusive(x_93);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_6);
lean_inc(x_100);
x_101 = lean_apply_3(x_1, x_100, x_6, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_apply_4(x_2, x_13, x_102, x_6, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
lean_free_object(x_93);
lean_dec(x_100);
x_107 = !lean_is_exclusive(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_104, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_ctor_set(x_104, 0, x_109);
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_104);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_104, 0);
lean_dec(x_114);
lean_ctor_set(x_104, 0, x_93);
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_dec(x_104);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_93);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_free_object(x_93);
lean_dec(x_100);
x_117 = !lean_is_exclusive(x_104);
if (x_117 == 0)
{
return x_104;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_104, 0);
x_119 = lean_ctor_get(x_104, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_104);
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
lean_free_object(x_93);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_101);
if (x_121 == 0)
{
return x_101;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_101, 0);
x_123 = lean_ctor_get(x_101, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_101);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_93, 0);
lean_inc(x_125);
lean_dec(x_93);
lean_inc(x_6);
lean_inc(x_125);
x_126 = lean_apply_3(x_1, x_125, x_6, x_98);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_apply_4(x_2, x_13, x_127, x_6, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
 x_137 = lean_box(0);
}
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_125);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_125);
x_140 = lean_ctor_get(x_129, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_142 = x_129;
} else {
 lean_dec_ref(x_129);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_125);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
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
}
}
else
{
uint8_t x_148; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_92);
if (x_148 == 0)
{
return x_92;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_92, 0);
x_150 = lean_ctor_get(x_92, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_92);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_box(0);
lean_ctor_set(x_11, 0, x_152);
return x_11;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_11, 0);
x_154 = lean_ctor_get(x_11, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_11);
x_155 = l_Lean_Expr_getAppFn___main(x_153);
x_156 = l_Lean_RecursorVal_getInduct(x_4);
x_157 = l_Lean_Expr_isConstOf(x_155, x_156);
lean_dec(x_156);
lean_dec(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
return x_159;
}
else
{
uint8_t x_160; 
x_160 = lean_expr_has_expr_mvar(x_153);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_4, 2);
lean_inc(x_161);
lean_dec(x_4);
x_162 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_163 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_162, x_153, x_161, x_6, x_154);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_169);
x_171 = lean_apply_3(x_1, x_169, x_6, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_apply_4(x_2, x_153, x_172, x_6, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_170);
lean_dec(x_169);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
x_179 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_182 = x_174;
} else {
 lean_dec_ref(x_174);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_170;
}
lean_ctor_set(x_183, 0, x_169);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_170);
lean_dec(x_169);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
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
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
x_189 = lean_ctor_get(x_171, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_191 = x_171;
} else {
 lean_dec_ref(x_171);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_163, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_163, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_195 = x_163;
} else {
 lean_dec_ref(x_163);
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
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Expr_getAppNumArgsAux___main(x_153, x_197);
x_199 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_198);
x_200 = lean_mk_array(x_198, x_199);
x_201 = lean_unsigned_to_nat(1u);
x_202 = lean_nat_sub(x_198, x_201);
lean_dec(x_198);
lean_inc(x_153);
x_203 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_153, x_200, x_202);
x_204 = lean_ctor_get(x_4, 2);
lean_inc(x_204);
lean_dec(x_4);
lean_inc(x_204);
x_205 = l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(x_203, x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_207 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_206, x_153, x_204, x_6, x_154);
lean_dec(x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_214 = x_208;
} else {
 lean_dec_ref(x_208);
 x_214 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_213);
x_215 = lean_apply_3(x_1, x_213, x_6, x_212);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_apply_4(x_2, x_153, x_216, x_6, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_214);
lean_dec(x_213);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_226 = x_218;
} else {
 lean_dec_ref(x_218);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_214;
}
lean_ctor_set(x_227, 0, x_213);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_214);
lean_dec(x_213);
x_229 = lean_ctor_get(x_218, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_231 = x_218;
} else {
 lean_dec_ref(x_218);
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
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
x_233 = lean_ctor_get(x_215, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_215, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_235 = x_215;
} else {
 lean_dec_ref(x_215);
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
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_207, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_207, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_239 = x_207;
} else {
 lean_dec_ref(x_207);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_204);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_154);
return x_242;
}
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_11);
if (x_243 == 0)
{
return x_11;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_11, 0);
x_245 = lean_ctor_get(x_11, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_11);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_8);
if (x_247 == 0)
{
return x_8;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_8, 0);
x_249 = lean_ctor_get(x_8, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_8);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_RecursorVal_getMajorIdx(x_7);
x_13 = lean_array_get_size(x_9);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_expr_eqv(x_5, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_9, x_12);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_19, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_65; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_65 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_66 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_21);
lean_inc(x_7);
x_67 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_7, x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_expr_eqv(x_5, x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_22);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_22);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Expr_getAppNumArgsAux___main(x_66, x_73);
x_75 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_74);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_66, x_76, x_78);
x_80 = l_List_lengthAux___main___rarg(x_8, x_73);
x_81 = lean_ctor_get(x_7, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_List_lengthAux___main___rarg(x_82, x_73);
x_84 = lean_nat_dec_eq(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_expr_eqv(x_5, x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_22);
return x_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_4);
lean_ctor_set(x_88, 1, x_22);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_4);
x_89 = lean_ctor_get(x_72, 2);
lean_inc(x_89);
x_90 = lean_instantiate_lparams(x_89, x_82, x_8);
x_91 = lean_ctor_get(x_7, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 4);
lean_inc(x_92);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
x_94 = lean_ctor_get(x_7, 5);
lean_inc(x_94);
lean_dec(x_7);
x_95 = lean_nat_add(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
x_96 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_95, x_9, x_73, x_90);
lean_dec(x_95);
x_97 = lean_array_get_size(x_79);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
lean_dec(x_72);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_97, x_79, x_99, x_96);
lean_dec(x_79);
lean_dec(x_97);
x_101 = lean_nat_add(x_12, x_77);
lean_dec(x_12);
x_102 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_13, x_9, x_101, x_100);
lean_dec(x_13);
x_103 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_102, x_10, x_22);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_inc(x_10);
lean_inc(x_21);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_104 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6(x_1, x_2, x_3, x_7, x_21, x_10, x_22);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_24 = x_21;
x_25 = x_106;
goto block_64;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_21);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
x_24 = x_108;
x_25 = x_107;
goto block_64;
}
}
else
{
uint8_t x_109; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_24);
lean_inc(x_7);
x_27 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_expr_eqv(x_5, x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_updateFn___main(x_4, x_6);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_33);
x_35 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_26, x_36, x_38);
x_40 = l_List_lengthAux___main___rarg(x_8, x_33);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_lengthAux___main___rarg(x_42, x_33);
x_44 = lean_nat_dec_eq(x_40, x_43);
lean_dec(x_43);
lean_dec(x_40);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_expr_eqv(x_5, x_6);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_4, x_6);
if (lean_is_scalar(x_23)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_23;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_25);
return x_47;
}
else
{
lean_object* x_48; 
if (lean_is_scalar(x_23)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_23;
}
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_25);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
lean_dec(x_4);
x_49 = lean_ctor_get(x_32, 2);
lean_inc(x_49);
x_50 = lean_instantiate_lparams(x_49, x_42, x_8);
x_51 = lean_ctor_get(x_7, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_7, 4);
lean_inc(x_52);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_7, 5);
lean_inc(x_54);
lean_dec(x_7);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_55, x_9, x_33, x_50);
lean_dec(x_55);
x_57 = lean_array_get_size(x_39);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_58);
x_60 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_57, x_39, x_59, x_56);
lean_dec(x_39);
lean_dec(x_57);
x_61 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
x_62 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_13, x_9, x_61, x_60);
lean_dec(x_13);
x_63 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_62, x_10, x_25);
return x_63;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_20);
if (x_113 == 0)
{
return x_20;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_20, 0);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_20);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = l_Lean_Expr_inhabited;
x_9 = l_monadInhabited___rarg(x_1, x_8);
x_10 = l_panicWithPos___rarg___closed__1;
x_11 = lean_string_append(x_10, x_2);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_4);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_panicWithPos___rarg___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_5);
x_23 = lean_panic_fn(x_22);
x_24 = lean_apply_2(x_23, x_6, x_7);
return x_24;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalDecl_valueOpt(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_4(x_11, lean_box(0), x_2, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9(x_3, x_4, x_5, x_1, x_13, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_4(x_10, lean_box(0), x_2, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9(x_3, x_4, x_5, x_1, x_12, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_unreachable_x21___rarg___closed__1;
x_14 = lean_unsigned_to_nat(37u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_unreachable_x21___rarg___closed__2;
x_17 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10(x_4, x_13, x_14, x_15, x_16, x_6, x_7);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_19__getLocalDecl), 3, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1___boxed), 8, 5);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_3);
x_22 = lean_apply_6(x_19, lean_box(0), lean_box(0), x_20, x_21, x_6, x_7);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_14__getMVarAssignment___boxed), 3, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__2), 8, 5);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_5);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
x_27 = lean_apply_6(x_24, lean_box(0), lean_box(0), x_25, x_26, x_6, x_7);
return x_27;
}
case 4:
{
lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
x_30 = l_Lean_Expr_getAppFn___main(x_29);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_30);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_30, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Expr_isLambda(x_33);
if (x_35 == 0)
{
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_31);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = l___private_Init_Lean_Meta_17__getConst(x_36, x_6, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_33);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
switch (lean_obj_tag(x_49)) {
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_ConstantInfo_name(x_49);
x_52 = l___private_Init_Lean_Meta_18__isAuxDef_x3f(x_51, x_6, x_50);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_52, 0, x_5);
return x_52;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_33);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_65);
x_67 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_66);
x_68 = lean_mk_array(x_66, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_66, x_69);
lean_dec(x_66);
lean_inc(x_5);
x_71 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_68, x_70);
x_72 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3(x_1, x_2, x_3, x_5, x_30, x_33, x_49, x_37, x_71, x_6, x_64);
lean_dec(x_33);
lean_dec(x_30);
return x_72;
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_dec(x_38);
x_74 = lean_ctor_get(x_49, 0);
lean_inc(x_74);
lean_dec(x_49);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_75);
x_77 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
lean_inc(x_5);
x_81 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_78, x_80);
x_82 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4(x_1, x_2, x_3, x_5, x_30, x_33, x_74, x_37, x_81, x_6, x_73);
lean_dec(x_81);
lean_dec(x_37);
lean_dec(x_74);
lean_dec(x_33);
lean_dec(x_30);
return x_82;
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
lean_dec(x_38);
x_84 = lean_ctor_get(x_49, 0);
lean_inc(x_84);
lean_dec(x_49);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_85);
x_87 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_86);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_86, x_89);
lean_dec(x_86);
lean_inc(x_5);
x_91 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_88, x_90);
x_92 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5(x_1, x_2, x_3, x_5, x_30, x_33, x_84, x_37, x_91, x_6, x_83);
lean_dec(x_91);
lean_dec(x_33);
lean_dec(x_30);
return x_92;
}
default: 
{
uint8_t x_93; 
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_38);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_96);
return x_38;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_38, 1);
lean_inc(x_97);
lean_dec(x_38);
x_98 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_33);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_38);
if (x_102 == 0)
{
return x_38;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_38, 0);
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_38);
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_107);
return x_31;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_5);
return x_31;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_31);
lean_dec(x_33);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_108);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
x_111 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_110);
x_112 = l_Lean_Expr_betaRev(x_30, x_111);
lean_dec(x_30);
x_113 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_112, x_6, x_34);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_31, 0);
x_115 = lean_ctor_get(x_31, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_31);
x_116 = l_Lean_Expr_isLambda(x_114);
if (x_116 == 0)
{
if (lean_obj_tag(x_114) == 4)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = l___private_Init_Lean_Meta_17__getConst(x_117, x_6, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
else
{
lean_object* x_126; 
lean_dec(x_114);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_5);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
lean_dec(x_120);
switch (lean_obj_tag(x_127)) {
case 1:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
lean_dec(x_119);
x_129 = l_Lean_ConstantInfo_name(x_127);
x_130 = l___private_Init_Lean_Meta_18__isAuxDef_x3f(x_129, x_6, x_128);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_127);
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_114);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
lean_dec(x_130);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_140);
x_142 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_141);
x_143 = lean_mk_array(x_141, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_sub(x_141, x_144);
lean_dec(x_141);
lean_inc(x_5);
x_146 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_143, x_145);
x_147 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3(x_1, x_2, x_3, x_5, x_30, x_114, x_127, x_118, x_146, x_6, x_139);
lean_dec(x_114);
lean_dec(x_30);
return x_147;
}
}
case 4:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
lean_dec(x_119);
x_149 = lean_ctor_get(x_127, 0);
lean_inc(x_149);
lean_dec(x_127);
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_150);
x_152 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_151);
x_153 = lean_mk_array(x_151, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_sub(x_151, x_154);
lean_dec(x_151);
lean_inc(x_5);
x_156 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_153, x_155);
x_157 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4(x_1, x_2, x_3, x_5, x_30, x_114, x_149, x_118, x_156, x_6, x_148);
lean_dec(x_156);
lean_dec(x_118);
lean_dec(x_149);
lean_dec(x_114);
lean_dec(x_30);
return x_157;
}
case 7:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_119, 1);
lean_inc(x_158);
lean_dec(x_119);
x_159 = lean_ctor_get(x_127, 0);
lean_inc(x_159);
lean_dec(x_127);
x_160 = lean_unsigned_to_nat(0u);
x_161 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_160);
x_162 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_161);
x_163 = lean_mk_array(x_161, x_162);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_sub(x_161, x_164);
lean_dec(x_161);
lean_inc(x_5);
x_166 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_163, x_165);
x_167 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5(x_1, x_2, x_3, x_5, x_30, x_114, x_159, x_118, x_166, x_6, x_158);
lean_dec(x_166);
lean_dec(x_114);
lean_dec(x_30);
return x_167;
}
default: 
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_127);
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_119, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_169 = x_119;
} else {
 lean_dec_ref(x_119);
 x_169 = lean_box(0);
}
x_170 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_114);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_5);
lean_ctor_set(x_173, 1, x_168);
return x_173;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_118);
lean_dec(x_114);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_119, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_119, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_176 = x_119;
} else {
 lean_dec_ref(x_119);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8_t x_178; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_115);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_114);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_5);
lean_ctor_set(x_181, 1, x_115);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_114);
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_182);
x_184 = lean_mk_empty_array_with_capacity(x_183);
lean_dec(x_183);
x_185 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_184);
x_186 = l_Lean_Expr_betaRev(x_30, x_185);
lean_dec(x_30);
x_187 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_186, x_6, x_115);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_31);
if (x_188 == 0)
{
return x_31;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_31, 0);
x_190 = lean_ctor_get(x_31, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_31);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 8:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_4);
x_192 = lean_ctor_get(x_5, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_5, 3);
lean_inc(x_193);
lean_dec(x_5);
x_194 = lean_expr_instantiate1(x_193, x_192);
lean_dec(x_192);
lean_dec(x_193);
x_195 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_194, x_6, x_7);
return x_195;
}
case 10:
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_5, 1);
lean_inc(x_196);
lean_dec(x_5);
x_5 = x_196;
goto _start;
}
case 11:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_4);
x_198 = lean_ctor_get(x_5, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_5, 2);
lean_inc(x_199);
lean_inc(x_6);
x_200 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_199, x_6, x_7);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
x_204 = l_Lean_Expr_getAppFn___main(x_202);
if (lean_obj_tag(x_204) == 4)
{
lean_object* x_205; lean_object* x_206; 
lean_free_object(x_200);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l___private_Init_Lean_Meta_17__getConst(x_205, x_6, x_203);
lean_dec(x_6);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_202);
lean_dec(x_198);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
lean_ctor_set(x_206, 0, x_5);
return x_206;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_5);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
lean_dec(x_207);
if (lean_obj_tag(x_212) == 6)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_206);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_214 = lean_ctor_get(x_206, 0);
lean_dec(x_214);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_nat_add(x_216, x_198);
lean_dec(x_198);
lean_dec(x_216);
x_218 = lean_unsigned_to_nat(0u);
x_219 = l_Lean_Expr_getAppNumArgsAux___main(x_202, x_218);
x_220 = lean_nat_sub(x_219, x_217);
lean_dec(x_217);
lean_dec(x_219);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_sub(x_220, x_221);
lean_dec(x_220);
x_223 = l_Lean_Expr_getRevArgD___main(x_202, x_222, x_5);
lean_dec(x_5);
lean_dec(x_202);
lean_ctor_set(x_206, 0, x_223);
return x_206;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_ctor_get(x_206, 1);
lean_inc(x_224);
lean_dec(x_206);
x_225 = lean_ctor_get(x_212, 0);
lean_inc(x_225);
lean_dec(x_212);
x_226 = lean_ctor_get(x_225, 3);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_nat_add(x_226, x_198);
lean_dec(x_198);
lean_dec(x_226);
x_228 = lean_unsigned_to_nat(0u);
x_229 = l_Lean_Expr_getAppNumArgsAux___main(x_202, x_228);
x_230 = lean_nat_sub(x_229, x_227);
lean_dec(x_227);
lean_dec(x_229);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_nat_sub(x_230, x_231);
lean_dec(x_230);
x_233 = l_Lean_Expr_getRevArgD___main(x_202, x_232, x_5);
lean_dec(x_5);
lean_dec(x_202);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_224);
return x_234;
}
}
else
{
uint8_t x_235; 
lean_dec(x_212);
lean_dec(x_202);
lean_dec(x_198);
x_235 = !lean_is_exclusive(x_206);
if (x_235 == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_206, 0);
lean_dec(x_236);
lean_ctor_set(x_206, 0, x_5);
return x_206;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_206, 1);
lean_inc(x_237);
lean_dec(x_206);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_5);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_5);
x_239 = !lean_is_exclusive(x_206);
if (x_239 == 0)
{
return x_206;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_206, 0);
x_241 = lean_ctor_get(x_206, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_206);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_6);
lean_ctor_set(x_200, 0, x_5);
return x_200;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_200, 0);
x_244 = lean_ctor_get(x_200, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_200);
x_245 = l_Lean_Expr_getAppFn___main(x_243);
if (lean_obj_tag(x_245) == 4)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l___private_Init_Lean_Meta_17__getConst(x_246, x_6, x_244);
lean_dec(x_6);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_243);
lean_dec(x_198);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_5);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
lean_dec(x_248);
if (lean_obj_tag(x_252) == 6)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_ctor_get(x_255, 3);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_nat_add(x_256, x_198);
lean_dec(x_198);
lean_dec(x_256);
x_258 = lean_unsigned_to_nat(0u);
x_259 = l_Lean_Expr_getAppNumArgsAux___main(x_243, x_258);
x_260 = lean_nat_sub(x_259, x_257);
lean_dec(x_257);
lean_dec(x_259);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_sub(x_260, x_261);
lean_dec(x_260);
x_263 = l_Lean_Expr_getRevArgD___main(x_243, x_262, x_5);
lean_dec(x_5);
lean_dec(x_243);
if (lean_is_scalar(x_254)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_254;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_253);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_198);
x_265 = lean_ctor_get(x_247, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_266 = x_247;
} else {
 lean_dec_ref(x_247);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_5);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_243);
lean_dec(x_198);
lean_dec(x_5);
x_268 = lean_ctor_get(x_247, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_247, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_270 = x_247;
} else {
 lean_dec_ref(x_247);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_198);
lean_dec(x_6);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_5);
lean_ctor_set(x_272, 1, x_244);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_198);
lean_dec(x_6);
lean_dec(x_5);
x_273 = !lean_is_exclusive(x_200);
if (x_273 == 0)
{
return x_200;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_200, 0);
x_275 = lean_ctor_get(x_200, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_200);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
default: 
{
lean_object* x_277; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = lean_box(0);
x_8 = x_277;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_4(x_10, lean_box(0), x_5, x_6, x_7);
return x_11;
}
}
}
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1;
x_8 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9(x_1, x_2, x_3, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_ConstantInfo_lparams(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_lengthAux___main___rarg(x_6, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_instantiate_value_lparams(x_5, x_6);
x_16 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_15);
x_17 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_16, x_7, x_8);
return x_17;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l_Lean_ConstantInfo_lparams(x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthAux___main___rarg(x_12, x_13);
lean_dec(x_12);
x_15 = l_List_lengthAux___main___rarg(x_8, x_13);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_expr_eqv(x_5, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_21 = lean_instantiate_value_lparams(x_7, x_8);
x_22 = l_Lean_Expr_betaRev(x_21, x_9);
lean_dec(x_21);
x_23 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_22);
x_24 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_23, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_115; lean_object* x_116; 
x_115 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_116 = lean_box(x_115);
switch (lean_obj_tag(x_116)) {
case 2:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_unsigned_to_nat(5u);
x_118 = lean_unsigned_to_nat(3u);
x_12 = x_117;
x_13 = x_118;
goto block_114;
}
case 3:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_unsigned_to_nat(4u);
x_120 = lean_unsigned_to_nat(3u);
x_12 = x_119;
x_13 = x_120;
goto block_114;
}
default: 
{
uint8_t x_121; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_expr_eqv(x_5, x_6);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_11);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_4);
lean_ctor_set(x_124, 1, x_11);
return x_124;
}
}
}
block_114:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_9);
x_15 = lean_nat_dec_lt(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_expr_eqv(x_5, x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_9, x_12);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_20, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Init_Lean_Meta_17__getConst(x_28, x_10, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_expr_eqv(x_5, x_6);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_expr_eqv(x_5, x_6);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
x_43 = lean_box(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_4);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l_Lean_Expr_inhabited;
x_46 = lean_array_get(x_45, x_9, x_13);
x_47 = lean_expr_mk_app(x_46, x_27);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_12, x_48);
x_50 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_14, x_9, x_49, x_47);
lean_dec(x_14);
x_51 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_50, x_10, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_29, 0);
lean_dec(x_53);
x_54 = lean_expr_eqv(x_5, x_6);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_55);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_expr_eqv(x_5, x_6);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_29);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_29, 0);
lean_dec(x_62);
x_63 = lean_expr_eqv(x_5, x_6);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_29, 0, x_64);
return x_29;
}
else
{
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_expr_eqv(x_5, x_6);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
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
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_21);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_21, 0);
lean_dec(x_75);
x_76 = lean_expr_eqv(x_5, x_6);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_77);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
lean_dec(x_21);
x_79 = lean_expr_eqv(x_5, x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_21);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_21, 0);
lean_dec(x_84);
x_85 = lean_expr_eqv(x_5, x_6);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_86);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_21, 1);
lean_inc(x_87);
lean_dec(x_21);
x_88 = lean_expr_eqv(x_5, x_6);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_4);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_21);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_21, 0);
lean_dec(x_93);
x_94 = lean_expr_eqv(x_5, x_6);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_95);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_dec(x_21);
x_97 = lean_expr_eqv(x_5, x_6);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_4);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_21);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_21, 0);
lean_dec(x_102);
x_103 = lean_expr_eqv(x_5, x_6);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Expr_updateFn___main(x_4, x_6);
lean_ctor_set(x_21, 0, x_104);
return x_21;
}
else
{
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_21, 1);
lean_inc(x_105);
lean_dec(x_21);
x_106 = lean_expr_eqv(x_5, x_6);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_4);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_21);
if (x_110 == 0)
{
return x_21;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_21, 0);
x_112 = lean_ctor_get(x_21, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_21);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn___main(x_13);
x_16 = l_Lean_RecursorVal_getInduct(x_4);
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
uint8_t x_19; 
x_19 = lean_expr_has_expr_mvar(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_11);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_22 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_21, x_13, x_20, x_6, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_6);
lean_inc(x_30);
x_31 = lean_apply_3(x_1, x_30, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_4(x_2, x_13, x_32, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_23);
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_23);
lean_dec(x_30);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
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
lean_free_object(x_23);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
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
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_55);
x_56 = lean_apply_3(x_1, x_55, x_6, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_apply_4(x_2, x_13, x_57, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
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
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_55);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_22);
if (x_78 == 0)
{
return x_22;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_22, 0);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_22);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_82);
x_84 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
lean_inc(x_13);
x_88 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_13, x_85, x_87);
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
lean_dec(x_4);
lean_inc(x_89);
x_90 = l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_free_object(x_11);
x_91 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_92 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_91, x_13, x_89, x_6, x_14);
lean_dec(x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_dec(x_92);
x_99 = !lean_is_exclusive(x_93);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_6);
lean_inc(x_100);
x_101 = lean_apply_3(x_1, x_100, x_6, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_apply_4(x_2, x_13, x_102, x_6, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
lean_free_object(x_93);
lean_dec(x_100);
x_107 = !lean_is_exclusive(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_104, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_ctor_set(x_104, 0, x_109);
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_104);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_104, 0);
lean_dec(x_114);
lean_ctor_set(x_104, 0, x_93);
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_dec(x_104);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_93);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_free_object(x_93);
lean_dec(x_100);
x_117 = !lean_is_exclusive(x_104);
if (x_117 == 0)
{
return x_104;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_104, 0);
x_119 = lean_ctor_get(x_104, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_104);
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
lean_free_object(x_93);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_101);
if (x_121 == 0)
{
return x_101;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_101, 0);
x_123 = lean_ctor_get(x_101, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_101);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_93, 0);
lean_inc(x_125);
lean_dec(x_93);
lean_inc(x_6);
lean_inc(x_125);
x_126 = lean_apply_3(x_1, x_125, x_6, x_98);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_apply_4(x_2, x_13, x_127, x_6, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
 x_137 = lean_box(0);
}
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_125);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_125);
x_140 = lean_ctor_get(x_129, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_142 = x_129;
} else {
 lean_dec_ref(x_129);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_125);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
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
}
}
else
{
uint8_t x_148; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_92);
if (x_148 == 0)
{
return x_92;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_92, 0);
x_150 = lean_ctor_get(x_92, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_92);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_89);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_box(0);
lean_ctor_set(x_11, 0, x_152);
return x_11;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_11, 0);
x_154 = lean_ctor_get(x_11, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_11);
x_155 = l_Lean_Expr_getAppFn___main(x_153);
x_156 = l_Lean_RecursorVal_getInduct(x_4);
x_157 = l_Lean_Expr_isConstOf(x_155, x_156);
lean_dec(x_156);
lean_dec(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
return x_159;
}
else
{
uint8_t x_160; 
x_160 = lean_expr_has_expr_mvar(x_153);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_4, 2);
lean_inc(x_161);
lean_dec(x_4);
x_162 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_163 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_162, x_153, x_161, x_6, x_154);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_169);
x_171 = lean_apply_3(x_1, x_169, x_6, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_apply_4(x_2, x_153, x_172, x_6, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_170);
lean_dec(x_169);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
x_179 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_182 = x_174;
} else {
 lean_dec_ref(x_174);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_170;
}
lean_ctor_set(x_183, 0, x_169);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_170);
lean_dec(x_169);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
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
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
x_189 = lean_ctor_get(x_171, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_191 = x_171;
} else {
 lean_dec_ref(x_171);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_163, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_163, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_195 = x_163;
} else {
 lean_dec_ref(x_163);
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
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Expr_getAppNumArgsAux___main(x_153, x_197);
x_199 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_198);
x_200 = lean_mk_array(x_198, x_199);
x_201 = lean_unsigned_to_nat(1u);
x_202 = lean_nat_sub(x_198, x_201);
lean_dec(x_198);
lean_inc(x_153);
x_203 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_153, x_200, x_202);
x_204 = lean_ctor_get(x_4, 2);
lean_inc(x_204);
lean_dec(x_4);
lean_inc(x_204);
x_205 = l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(x_203, x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_207 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_206, x_153, x_204, x_6, x_154);
lean_dec(x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_214 = x_208;
} else {
 lean_dec_ref(x_208);
 x_214 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_213);
x_215 = lean_apply_3(x_1, x_213, x_6, x_212);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_apply_4(x_2, x_153, x_216, x_6, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_214);
lean_dec(x_213);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_226 = x_218;
} else {
 lean_dec_ref(x_218);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_214;
}
lean_ctor_set(x_227, 0, x_213);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_214);
lean_dec(x_213);
x_229 = lean_ctor_get(x_218, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_231 = x_218;
} else {
 lean_dec_ref(x_218);
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
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
x_233 = lean_ctor_get(x_215, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_215, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_235 = x_215;
} else {
 lean_dec_ref(x_215);
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
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_207, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_207, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_239 = x_207;
} else {
 lean_dec_ref(x_207);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_204);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_154);
return x_242;
}
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_11);
if (x_243 == 0)
{
return x_11;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_11, 0);
x_245 = lean_ctor_get(x_11, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_11);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_8);
if (x_247 == 0)
{
return x_8;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_8, 0);
x_249 = lean_ctor_get(x_8, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_8);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_RecursorVal_getMajorIdx(x_7);
x_13 = lean_array_get_size(x_9);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_expr_eqv(x_5, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_9, x_12);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_19, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_65; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_65 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_66 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_21);
lean_inc(x_7);
x_67 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_7, x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_expr_eqv(x_5, x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_22);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_22);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Expr_getAppNumArgsAux___main(x_66, x_73);
x_75 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_74);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_66, x_76, x_78);
x_80 = l_List_lengthAux___main___rarg(x_8, x_73);
x_81 = lean_ctor_get(x_7, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_List_lengthAux___main___rarg(x_82, x_73);
x_84 = lean_nat_dec_eq(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_expr_eqv(x_5, x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_updateFn___main(x_4, x_6);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_22);
return x_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_4);
lean_ctor_set(x_88, 1, x_22);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_4);
x_89 = lean_ctor_get(x_72, 2);
lean_inc(x_89);
x_90 = lean_instantiate_lparams(x_89, x_82, x_8);
x_91 = lean_ctor_get(x_7, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 4);
lean_inc(x_92);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
x_94 = lean_ctor_get(x_7, 5);
lean_inc(x_94);
lean_dec(x_7);
x_95 = lean_nat_add(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
x_96 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_95, x_9, x_73, x_90);
lean_dec(x_95);
x_97 = lean_array_get_size(x_79);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
lean_dec(x_72);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_97, x_79, x_99, x_96);
lean_dec(x_79);
lean_dec(x_97);
x_101 = lean_nat_add(x_12, x_77);
lean_dec(x_12);
x_102 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_13, x_9, x_101, x_100);
lean_dec(x_13);
x_103 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_102, x_10, x_22);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_inc(x_10);
lean_inc(x_21);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_104 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__20(x_1, x_2, x_3, x_7, x_21, x_10, x_22);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_24 = x_21;
x_25 = x_106;
goto block_64;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_21);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
x_24 = x_108;
x_25 = x_107;
goto block_64;
}
}
else
{
uint8_t x_109; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Init_Lean_WHNF_3__toCtorIfLit(x_24);
lean_inc(x_7);
x_27 = l___private_Init_Lean_WHNF_4__getRecRuleFor(x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_expr_eqv(x_5, x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_updateFn___main(x_4, x_6);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_33);
x_35 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_26, x_36, x_38);
x_40 = l_List_lengthAux___main___rarg(x_8, x_33);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_lengthAux___main___rarg(x_42, x_33);
x_44 = lean_nat_dec_eq(x_40, x_43);
lean_dec(x_43);
lean_dec(x_40);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_expr_eqv(x_5, x_6);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_4, x_6);
if (lean_is_scalar(x_23)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_23;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_25);
return x_47;
}
else
{
lean_object* x_48; 
if (lean_is_scalar(x_23)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_23;
}
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_25);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
lean_dec(x_4);
x_49 = lean_ctor_get(x_32, 2);
lean_inc(x_49);
x_50 = lean_instantiate_lparams(x_49, x_42, x_8);
x_51 = lean_ctor_get(x_7, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_7, 4);
lean_inc(x_52);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_7, 5);
lean_inc(x_54);
lean_dec(x_7);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_55, x_9, x_33, x_50);
lean_dec(x_55);
x_57 = lean_array_get_size(x_39);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_58);
x_60 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_57, x_39, x_59, x_56);
lean_dec(x_39);
lean_dec(x_57);
x_61 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
x_62 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_13, x_9, x_61, x_60);
lean_dec(x_13);
x_63 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_62, x_10, x_25);
return x_63;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_20);
if (x_113 == 0)
{
return x_20;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_20, 0);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_20);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = l_Lean_Expr_inhabited;
x_9 = l_monadInhabited___rarg(x_1, x_8);
x_10 = l_panicWithPos___rarg___closed__1;
x_11 = lean_string_append(x_10, x_2);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_4);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_panicWithPos___rarg___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_5);
x_23 = lean_panic_fn(x_22);
x_24 = lean_apply_2(x_23, x_6, x_7);
return x_24;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalDecl_valueOpt(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_4(x_11, lean_box(0), x_2, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21(x_3, x_4, x_5, x_1, x_13, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_4(x_10, lean_box(0), x_2, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21(x_3, x_4, x_5, x_1, x_12, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_unreachable_x21___rarg___closed__1;
x_14 = lean_unsigned_to_nat(37u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_unreachable_x21___rarg___closed__2;
x_17 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22(x_4, x_13, x_14, x_15, x_16, x_6, x_7);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_19__getLocalDecl), 3, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1___boxed), 8, 5);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_3);
x_22 = lean_apply_6(x_19, lean_box(0), lean_box(0), x_20, x_21, x_6, x_7);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_14__getMVarAssignment___boxed), 3, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__2), 8, 5);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_5);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
x_27 = lean_apply_6(x_24, lean_box(0), lean_box(0), x_25, x_26, x_6, x_7);
return x_27;
}
case 4:
{
lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
x_30 = l_Lean_Expr_getAppFn___main(x_29);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_30);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_30, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Expr_isLambda(x_33);
if (x_35 == 0)
{
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_31);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = l___private_Init_Lean_Meta_17__getConst(x_36, x_6, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_33);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
switch (lean_obj_tag(x_49)) {
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_ConstantInfo_name(x_49);
x_52 = l___private_Init_Lean_Meta_18__isAuxDef_x3f(x_51, x_6, x_50);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_52, 0, x_5);
return x_52;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_33);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_65);
x_67 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_66);
x_68 = lean_mk_array(x_66, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_66, x_69);
lean_dec(x_66);
lean_inc(x_5);
x_71 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_68, x_70);
x_72 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17(x_1, x_2, x_3, x_5, x_30, x_33, x_49, x_37, x_71, x_6, x_64);
lean_dec(x_33);
lean_dec(x_30);
return x_72;
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_dec(x_38);
x_74 = lean_ctor_get(x_49, 0);
lean_inc(x_74);
lean_dec(x_49);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_75);
x_77 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
lean_inc(x_5);
x_81 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_78, x_80);
x_82 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18(x_1, x_2, x_3, x_5, x_30, x_33, x_74, x_37, x_81, x_6, x_73);
lean_dec(x_81);
lean_dec(x_37);
lean_dec(x_74);
lean_dec(x_33);
lean_dec(x_30);
return x_82;
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
lean_dec(x_38);
x_84 = lean_ctor_get(x_49, 0);
lean_inc(x_84);
lean_dec(x_49);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_85);
x_87 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_86);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_86, x_89);
lean_dec(x_86);
lean_inc(x_5);
x_91 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_88, x_90);
x_92 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19(x_1, x_2, x_3, x_5, x_30, x_33, x_84, x_37, x_91, x_6, x_83);
lean_dec(x_91);
lean_dec(x_33);
lean_dec(x_30);
return x_92;
}
default: 
{
uint8_t x_93; 
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_38);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_96);
return x_38;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_38, 1);
lean_inc(x_97);
lean_dec(x_38);
x_98 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_33);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_38);
if (x_102 == 0)
{
return x_38;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_38, 0);
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_38);
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_expr_eqv(x_30, x_33);
lean_dec(x_30);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_Expr_updateFn___main(x_5, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_107);
return x_31;
}
else
{
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_5);
return x_31;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_31);
lean_dec(x_33);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_108);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
x_111 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_110);
x_112 = l_Lean_Expr_betaRev(x_30, x_111);
lean_dec(x_30);
x_113 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_112, x_6, x_34);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_31, 0);
x_115 = lean_ctor_get(x_31, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_31);
x_116 = l_Lean_Expr_isLambda(x_114);
if (x_116 == 0)
{
if (lean_obj_tag(x_114) == 4)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = l___private_Init_Lean_Meta_17__getConst(x_117, x_6, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
else
{
lean_object* x_126; 
lean_dec(x_114);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_5);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
lean_dec(x_120);
switch (lean_obj_tag(x_127)) {
case 1:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
lean_dec(x_119);
x_129 = l_Lean_ConstantInfo_name(x_127);
x_130 = l___private_Init_Lean_Meta_18__isAuxDef_x3f(x_129, x_6, x_128);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_127);
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_114);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
lean_dec(x_130);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_140);
x_142 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_141);
x_143 = lean_mk_array(x_141, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_sub(x_141, x_144);
lean_dec(x_141);
lean_inc(x_5);
x_146 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_143, x_145);
x_147 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17(x_1, x_2, x_3, x_5, x_30, x_114, x_127, x_118, x_146, x_6, x_139);
lean_dec(x_114);
lean_dec(x_30);
return x_147;
}
}
case 4:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
lean_dec(x_119);
x_149 = lean_ctor_get(x_127, 0);
lean_inc(x_149);
lean_dec(x_127);
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_150);
x_152 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_151);
x_153 = lean_mk_array(x_151, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_sub(x_151, x_154);
lean_dec(x_151);
lean_inc(x_5);
x_156 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_153, x_155);
x_157 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18(x_1, x_2, x_3, x_5, x_30, x_114, x_149, x_118, x_156, x_6, x_148);
lean_dec(x_156);
lean_dec(x_118);
lean_dec(x_149);
lean_dec(x_114);
lean_dec(x_30);
return x_157;
}
case 7:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_119, 1);
lean_inc(x_158);
lean_dec(x_119);
x_159 = lean_ctor_get(x_127, 0);
lean_inc(x_159);
lean_dec(x_127);
x_160 = lean_unsigned_to_nat(0u);
x_161 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_160);
x_162 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_161);
x_163 = lean_mk_array(x_161, x_162);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_sub(x_161, x_164);
lean_dec(x_161);
lean_inc(x_5);
x_166 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_163, x_165);
x_167 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19(x_1, x_2, x_3, x_5, x_30, x_114, x_159, x_118, x_166, x_6, x_158);
lean_dec(x_166);
lean_dec(x_114);
lean_dec(x_30);
return x_167;
}
default: 
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_127);
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_119, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_169 = x_119;
} else {
 lean_dec_ref(x_119);
 x_169 = lean_box(0);
}
x_170 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_114);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_5);
lean_ctor_set(x_173, 1, x_168);
return x_173;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_118);
lean_dec(x_114);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_119, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_119, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_176 = x_119;
} else {
 lean_dec_ref(x_119);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8_t x_178; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_expr_eqv(x_30, x_114);
lean_dec(x_30);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_Expr_updateFn___main(x_5, x_114);
lean_dec(x_114);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_115);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_114);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_5);
lean_ctor_set(x_181, 1, x_115);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_114);
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_182);
x_184 = lean_mk_empty_array_with_capacity(x_183);
lean_dec(x_183);
x_185 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_184);
x_186 = l_Lean_Expr_betaRev(x_30, x_185);
lean_dec(x_30);
x_187 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_186, x_6, x_115);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_31);
if (x_188 == 0)
{
return x_31;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_31, 0);
x_190 = lean_ctor_get(x_31, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_31);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 8:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_4);
x_192 = lean_ctor_get(x_5, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_5, 3);
lean_inc(x_193);
lean_dec(x_5);
x_194 = lean_expr_instantiate1(x_193, x_192);
lean_dec(x_192);
lean_dec(x_193);
x_195 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_194, x_6, x_7);
return x_195;
}
case 10:
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_5, 1);
lean_inc(x_196);
lean_dec(x_5);
x_5 = x_196;
goto _start;
}
case 11:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_4);
x_198 = lean_ctor_get(x_5, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_5, 2);
lean_inc(x_199);
lean_inc(x_6);
x_200 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_199, x_6, x_7);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
x_204 = l_Lean_Expr_getAppFn___main(x_202);
if (lean_obj_tag(x_204) == 4)
{
lean_object* x_205; lean_object* x_206; 
lean_free_object(x_200);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l___private_Init_Lean_Meta_17__getConst(x_205, x_6, x_203);
lean_dec(x_6);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_202);
lean_dec(x_198);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
lean_ctor_set(x_206, 0, x_5);
return x_206;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_5);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
lean_dec(x_207);
if (lean_obj_tag(x_212) == 6)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_206);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_214 = lean_ctor_get(x_206, 0);
lean_dec(x_214);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_nat_add(x_216, x_198);
lean_dec(x_198);
lean_dec(x_216);
x_218 = lean_unsigned_to_nat(0u);
x_219 = l_Lean_Expr_getAppNumArgsAux___main(x_202, x_218);
x_220 = lean_nat_sub(x_219, x_217);
lean_dec(x_217);
lean_dec(x_219);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_sub(x_220, x_221);
lean_dec(x_220);
x_223 = l_Lean_Expr_getRevArgD___main(x_202, x_222, x_5);
lean_dec(x_5);
lean_dec(x_202);
lean_ctor_set(x_206, 0, x_223);
return x_206;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_ctor_get(x_206, 1);
lean_inc(x_224);
lean_dec(x_206);
x_225 = lean_ctor_get(x_212, 0);
lean_inc(x_225);
lean_dec(x_212);
x_226 = lean_ctor_get(x_225, 3);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_nat_add(x_226, x_198);
lean_dec(x_198);
lean_dec(x_226);
x_228 = lean_unsigned_to_nat(0u);
x_229 = l_Lean_Expr_getAppNumArgsAux___main(x_202, x_228);
x_230 = lean_nat_sub(x_229, x_227);
lean_dec(x_227);
lean_dec(x_229);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_nat_sub(x_230, x_231);
lean_dec(x_230);
x_233 = l_Lean_Expr_getRevArgD___main(x_202, x_232, x_5);
lean_dec(x_5);
lean_dec(x_202);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_224);
return x_234;
}
}
else
{
uint8_t x_235; 
lean_dec(x_212);
lean_dec(x_202);
lean_dec(x_198);
x_235 = !lean_is_exclusive(x_206);
if (x_235 == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_206, 0);
lean_dec(x_236);
lean_ctor_set(x_206, 0, x_5);
return x_206;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_206, 1);
lean_inc(x_237);
lean_dec(x_206);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_5);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_5);
x_239 = !lean_is_exclusive(x_206);
if (x_239 == 0)
{
return x_206;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_206, 0);
x_241 = lean_ctor_get(x_206, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_206);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_6);
lean_ctor_set(x_200, 0, x_5);
return x_200;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_200, 0);
x_244 = lean_ctor_get(x_200, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_200);
x_245 = l_Lean_Expr_getAppFn___main(x_243);
if (lean_obj_tag(x_245) == 4)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l___private_Init_Lean_Meta_17__getConst(x_246, x_6, x_244);
lean_dec(x_6);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_243);
lean_dec(x_198);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_5);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
lean_dec(x_248);
if (lean_obj_tag(x_252) == 6)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_ctor_get(x_255, 3);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_nat_add(x_256, x_198);
lean_dec(x_198);
lean_dec(x_256);
x_258 = lean_unsigned_to_nat(0u);
x_259 = l_Lean_Expr_getAppNumArgsAux___main(x_243, x_258);
x_260 = lean_nat_sub(x_259, x_257);
lean_dec(x_257);
lean_dec(x_259);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_sub(x_260, x_261);
lean_dec(x_260);
x_263 = l_Lean_Expr_getRevArgD___main(x_243, x_262, x_5);
lean_dec(x_5);
lean_dec(x_243);
if (lean_is_scalar(x_254)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_254;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_253);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_198);
x_265 = lean_ctor_get(x_247, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_266 = x_247;
} else {
 lean_dec_ref(x_247);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_5);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_243);
lean_dec(x_198);
lean_dec(x_5);
x_268 = lean_ctor_get(x_247, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_247, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_270 = x_247;
} else {
 lean_dec_ref(x_247);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; 
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_198);
lean_dec(x_6);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_5);
lean_ctor_set(x_272, 1, x_244);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_198);
lean_dec(x_6);
lean_dec(x_5);
x_273 = !lean_is_exclusive(x_200);
if (x_273 == 0)
{
return x_200;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_200, 0);
x_275 = lean_ctor_get(x_200, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_200);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
default: 
{
lean_object* x_277; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = lean_box(0);
x_8 = x_277;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_4(x_10, lean_box(0), x_5, x_6, x_7);
return x_11;
}
}
}
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1;
x_8 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21(x_1, x_2, x_3, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_24; lean_object* x_25; 
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_25 = lean_box(x_24);
switch (lean_obj_tag(x_25)) {
case 2:
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(5u);
x_9 = x_26;
goto block_23;
}
case 3:
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(4u);
x_9 = x_27;
goto block_23;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
block_23:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_6, x_9);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__23(x_1, x_2, x_3, x_16, x_7, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
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
}
}
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_RecursorVal_getMajorIdx(x_4);
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_6, x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_15, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__23(x_1, x_2, x_3, x_17, x_7, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
}
lean_object* l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 2:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_Expr_getAppFn___main(x_9);
lean_dec(x_9);
switch (lean_obj_tag(x_10)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l___private_Init_Lean_Meta_17__getConst(x_13, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
switch (lean_obj_tag(x_23)) {
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_26);
x_28 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_29, x_31);
x_33 = l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24(x_1, x_2, x_3, x_25, x_14, x_32, x_5, x_24);
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_25);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_36);
x_38 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_39, x_41);
x_43 = l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25(x_1, x_2, x_3, x_35, x_14, x_42, x_5, x_34);
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_35);
return x_43;
}
default: 
{
uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_15, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_15, 0, x_46);
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
default: 
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
case 10:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
lean_dec(x_4);
x_4 = x_56;
goto _start;
}
case 11:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_4, 2);
lean_inc(x_58);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_58, x_5, x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_4 = x_60;
x_6 = x_61;
goto _start;
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
default: 
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_6);
return x_68;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__16(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__23(x_1, x_2, x_3, x_8, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_5);
x_18 = lean_apply_3(x_3, x_17, x_5, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_4 = x_8;
x_6 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
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
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__15(x_1, x_2, x_3, x_18, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_19);
lean_dec(x_4);
x_24 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_21);
x_25 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_24, x_8, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = l___private_Init_Lean_WHNF_6__isIdRhsApp(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_30 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_26);
x_31 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_30, x_8, x_27);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_4);
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
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_ConstantInfo_lparams(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthAux___main___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = l_List_lengthAux___main___rarg(x_6, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_instantiate_value_lparams(x_5, x_6);
x_17 = l_Lean_Expr_betaRev(x_16, x_7);
lean_dec(x_16);
x_18 = l___private_Init_Lean_WHNF_7__extractIdRhs(x_17);
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l___private_Init_Lean_Meta_17__getConst(x_8, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__12(x_1, x_2, x_3, x_4, x_16, x_9, x_6, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
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
case 5:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
x_28 = l_Lean_Expr_getAppFn___main(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Init_Lean_Meta_17__getConst(x_29, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_4);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_31, 1);
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_Lean_ConstantInfo_lparams(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_List_lengthAux___main___rarg(x_41, x_42);
lean_dec(x_41);
x_44 = l_List_lengthAux___main___rarg(x_30, x_42);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_31, 0, x_4);
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_31);
x_46 = l_Lean_ConstantInfo_name(x_40);
x_47 = l_Lean_smartUnfoldingSuffix;
x_48 = lean_name_mk_string(x_46, x_47);
x_49 = l___private_Init_Lean_Meta_17__getConst(x_48, x_6, x_38);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_53 = lean_mk_empty_array_with_capacity(x_52);
lean_dec(x_52);
x_54 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_53);
x_55 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__13(x_1, x_2, x_3, x_4, x_40, x_30, x_54, x_6, x_51);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
switch (lean_obj_tag(x_56)) {
case 0:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_56);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_59);
x_61 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__14(x_1, x_2, x_3, x_4, x_40, x_30, x_60, x_6, x_57);
return x_61;
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_40);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_dec(x_49);
x_63 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_64 = lean_mk_empty_array_with_capacity(x_63);
lean_dec(x_63);
x_65 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_64);
x_66 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__26(x_1, x_2, x_3, x_4, x_56, x_30, x_65, x_6, x_62);
return x_66;
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_dec(x_49);
x_68 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_69 = lean_mk_empty_array_with_capacity(x_68);
lean_dec(x_68);
x_70 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_69);
x_71 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__27(x_1, x_2, x_3, x_4, x_40, x_30, x_70, x_6, x_67);
return x_71;
}
case 3:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_56);
x_72 = lean_ctor_get(x_49, 1);
lean_inc(x_72);
lean_dec(x_49);
x_73 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_74 = lean_mk_empty_array_with_capacity(x_73);
lean_dec(x_73);
x_75 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_74);
x_76 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__28(x_1, x_2, x_3, x_4, x_40, x_30, x_75, x_6, x_72);
return x_76;
}
case 4:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_79 = lean_mk_empty_array_with_capacity(x_78);
lean_dec(x_78);
x_80 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_79);
x_81 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__29(x_1, x_2, x_3, x_4, x_40, x_30, x_80, x_6, x_77);
return x_81;
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_56);
x_82 = lean_ctor_get(x_49, 1);
lean_inc(x_82);
lean_dec(x_49);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_84 = lean_mk_empty_array_with_capacity(x_83);
lean_dec(x_83);
x_85 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_84);
x_86 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__30(x_1, x_2, x_3, x_4, x_40, x_30, x_85, x_6, x_82);
return x_86;
}
case 6:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_56);
x_87 = lean_ctor_get(x_49, 1);
lean_inc(x_87);
lean_dec(x_49);
x_88 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_89 = lean_mk_empty_array_with_capacity(x_88);
lean_dec(x_88);
x_90 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_89);
x_91 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__31(x_1, x_2, x_3, x_4, x_40, x_30, x_90, x_6, x_87);
return x_91;
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_56);
x_92 = lean_ctor_get(x_49, 1);
lean_inc(x_92);
lean_dec(x_49);
x_93 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_42);
x_94 = lean_mk_empty_array_with_capacity(x_93);
lean_dec(x_93);
x_95 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_94);
x_96 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__32(x_1, x_2, x_3, x_4, x_40, x_30, x_95, x_6, x_92);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_49);
if (x_97 == 0)
{
return x_49;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_49, 0);
x_99 = lean_ctor_get(x_49, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_49);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_101 = lean_ctor_get(x_31, 1);
lean_inc(x_101);
lean_dec(x_31);
x_102 = lean_ctor_get(x_32, 0);
lean_inc(x_102);
lean_dec(x_32);
x_103 = l_Lean_ConstantInfo_lparams(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_List_lengthAux___main___rarg(x_103, x_104);
lean_dec(x_103);
x_106 = l_List_lengthAux___main___rarg(x_30, x_104);
x_107 = lean_nat_dec_eq(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_102);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_101);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = l_Lean_ConstantInfo_name(x_102);
x_110 = l_Lean_smartUnfoldingSuffix;
x_111 = lean_name_mk_string(x_109, x_110);
x_112 = l___private_Init_Lean_Meta_17__getConst(x_111, x_6, x_101);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_116 = lean_mk_empty_array_with_capacity(x_115);
lean_dec(x_115);
x_117 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_116);
x_118 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__13(x_1, x_2, x_3, x_4, x_102, x_30, x_117, x_6, x_114);
return x_118;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
lean_dec(x_113);
switch (lean_obj_tag(x_119)) {
case 0:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_119);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
lean_dec(x_112);
x_121 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_122 = lean_mk_empty_array_with_capacity(x_121);
lean_dec(x_121);
x_123 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_122);
x_124 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__14(x_1, x_2, x_3, x_4, x_102, x_30, x_123, x_6, x_120);
return x_124;
}
case 1:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_102);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
lean_dec(x_112);
x_126 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_127 = lean_mk_empty_array_with_capacity(x_126);
lean_dec(x_126);
x_128 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_127);
x_129 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__26(x_1, x_2, x_3, x_4, x_119, x_30, x_128, x_6, x_125);
return x_129;
}
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_119);
x_130 = lean_ctor_get(x_112, 1);
lean_inc(x_130);
lean_dec(x_112);
x_131 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_132 = lean_mk_empty_array_with_capacity(x_131);
lean_dec(x_131);
x_133 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_132);
x_134 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__27(x_1, x_2, x_3, x_4, x_102, x_30, x_133, x_6, x_130);
return x_134;
}
case 3:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_119);
x_135 = lean_ctor_get(x_112, 1);
lean_inc(x_135);
lean_dec(x_112);
x_136 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_137 = lean_mk_empty_array_with_capacity(x_136);
lean_dec(x_136);
x_138 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_137);
x_139 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__28(x_1, x_2, x_3, x_4, x_102, x_30, x_138, x_6, x_135);
return x_139;
}
case 4:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_119);
x_140 = lean_ctor_get(x_112, 1);
lean_inc(x_140);
lean_dec(x_112);
x_141 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_142 = lean_mk_empty_array_with_capacity(x_141);
lean_dec(x_141);
x_143 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_142);
x_144 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__29(x_1, x_2, x_3, x_4, x_102, x_30, x_143, x_6, x_140);
return x_144;
}
case 5:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_119);
x_145 = lean_ctor_get(x_112, 1);
lean_inc(x_145);
lean_dec(x_112);
x_146 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_147 = lean_mk_empty_array_with_capacity(x_146);
lean_dec(x_146);
x_148 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_147);
x_149 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__30(x_1, x_2, x_3, x_4, x_102, x_30, x_148, x_6, x_145);
return x_149;
}
case 6:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_119);
x_150 = lean_ctor_get(x_112, 1);
lean_inc(x_150);
lean_dec(x_112);
x_151 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_152 = lean_mk_empty_array_with_capacity(x_151);
lean_dec(x_151);
x_153 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_152);
x_154 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__31(x_1, x_2, x_3, x_4, x_102, x_30, x_153, x_6, x_150);
return x_154;
}
default: 
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_119);
x_155 = lean_ctor_get(x_112, 1);
lean_inc(x_155);
lean_dec(x_112);
x_156 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_104);
x_157 = lean_mk_empty_array_with_capacity(x_156);
lean_dec(x_156);
x_158 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_5, x_157);
x_159 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__32(x_1, x_2, x_3, x_4, x_102, x_30, x_158, x_6, x_155);
return x_159;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_102);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_112, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_112, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_162 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_31);
if (x_164 == 0)
{
return x_31;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_31, 0);
x_166 = lean_ctor_get(x_31, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_31);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_4);
lean_ctor_set(x_168, 1, x_7);
return x_168;
}
}
default: 
{
lean_object* x_169; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_4);
lean_ctor_set(x_169, 1, x_7);
return x_169;
}
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_unreachable_x21___rarg___closed__1;
x_8 = lean_unsigned_to_nat(37u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_unreachable_x21___rarg___closed__2;
x_11 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_inc(x_5);
x_13 = l___private_Init_Lean_Meta_19__getLocalDecl(x_12, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_LocalDecl_valueOpt(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_4 = x_18;
x_6 = x_16;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_LocalDecl_valueOpt(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_4 = x_24;
x_6 = x_21;
goto _start;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
x_32 = lean_metavar_ctx_get_expr_assignment(x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_4 = x_34;
goto _start;
}
}
case 4:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*1 + 4);
lean_dec(x_36);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(x_37);
lean_inc(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_39, x_41);
lean_dec(x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc_n(x_44, 2);
x_46 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(x_1, x_2, x_3, x_44, x_44, x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_47, 2);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_box(x_37);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_44);
lean_inc(x_50);
x_58 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_55, x_57, x_50);
lean_ctor_set(x_48, 0, x_58);
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_box(x_37);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_44);
lean_inc(x_50);
x_63 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_59, x_62, x_50);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_47, 2, x_64);
return x_46;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 3);
x_68 = lean_ctor_get(x_47, 4);
x_69 = lean_ctor_get(x_47, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_47);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_72 = x_48;
} else {
 lean_dec_ref(x_48);
 x_72 = lean_box(0);
}
x_73 = lean_box(x_37);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_44);
lean_inc(x_50);
x_75 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_70, x_74, x_50);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_68);
lean_ctor_set(x_77, 5, x_69);
lean_ctor_set(x_46, 1, x_77);
return x_46;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_78 = lean_ctor_get(x_46, 0);
lean_inc(x_78);
lean_dec(x_46);
x_79 = lean_ctor_get(x_47, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_47, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 5);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_48, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_48, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_87 = x_48;
} else {
 lean_dec_ref(x_48);
 x_87 = lean_box(0);
}
x_88 = lean_box(x_37);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_44);
lean_inc(x_78);
x_90 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_85, x_89, x_78);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 6, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_79);
lean_ctor_set(x_92, 1, x_80);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_81);
lean_ctor_set(x_92, 4, x_82);
lean_ctor_set(x_92, 5, x_83);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_44);
x_94 = !lean_is_exclusive(x_46);
if (x_94 == 0)
{
return x_46;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_46, 0);
x_96 = lean_ctor_get(x_46, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_46);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_43);
if (x_98 == 0)
{
return x_43;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_43, 0);
x_100 = lean_ctor_get(x_43, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_43);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_42, 0);
lean_inc(x_102);
lean_dec(x_42);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_6);
return x_103;
}
}
case 5:
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_104, sizeof(void*)*1 + 4);
lean_dec(x_104);
x_106 = lean_ctor_get(x_6, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_box(x_105);
lean_inc(x_4);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_4);
x_110 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_107, x_109);
lean_dec(x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc_n(x_112, 2);
x_114 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(x_1, x_2, x_3, x_112, x_112, x_5, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 2);
lean_inc(x_116);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_115);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_115, 2);
lean_dec(x_121);
x_122 = !lean_is_exclusive(x_116);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_116, 0);
x_124 = lean_box(x_105);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_112);
lean_inc(x_118);
x_126 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_123, x_125, x_118);
lean_ctor_set(x_116, 0, x_126);
return x_114;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_116, 0);
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_116);
x_129 = lean_box(x_105);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_112);
lean_inc(x_118);
x_131 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_127, x_130, x_118);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_115, 2, x_132);
return x_114;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = lean_ctor_get(x_115, 0);
x_134 = lean_ctor_get(x_115, 1);
x_135 = lean_ctor_get(x_115, 3);
x_136 = lean_ctor_get(x_115, 4);
x_137 = lean_ctor_get(x_115, 5);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_115);
x_138 = lean_ctor_get(x_116, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_116, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_140 = x_116;
} else {
 lean_dec_ref(x_116);
 x_140 = lean_box(0);
}
x_141 = lean_box(x_105);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_112);
lean_inc(x_118);
x_143 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_138, x_142, x_118);
if (lean_is_scalar(x_140)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_140;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
x_145 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_145, 0, x_133);
lean_ctor_set(x_145, 1, x_134);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set(x_145, 3, x_135);
lean_ctor_set(x_145, 4, x_136);
lean_ctor_set(x_145, 5, x_137);
lean_ctor_set(x_114, 1, x_145);
return x_114;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_146 = lean_ctor_get(x_114, 0);
lean_inc(x_146);
lean_dec(x_114);
x_147 = lean_ctor_get(x_115, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_115, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_115, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_115, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_115, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 x_152 = x_115;
} else {
 lean_dec_ref(x_115);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_116, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_116, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_155 = x_116;
} else {
 lean_dec_ref(x_116);
 x_155 = lean_box(0);
}
x_156 = lean_box(x_105);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_112);
lean_inc(x_146);
x_158 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_153, x_157, x_146);
if (lean_is_scalar(x_155)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_155;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
if (lean_is_scalar(x_152)) {
 x_160 = lean_alloc_ctor(0, 6, 0);
} else {
 x_160 = x_152;
}
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_148);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_160, 3, x_149);
lean_ctor_set(x_160, 4, x_150);
lean_ctor_set(x_160, 5, x_151);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_112);
x_162 = !lean_is_exclusive(x_114);
if (x_162 == 0)
{
return x_114;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_114, 0);
x_164 = lean_ctor_get(x_114, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_114);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_111);
if (x_166 == 0)
{
return x_111;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_111, 0);
x_168 = lean_ctor_get(x_111, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_111);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_110, 0);
lean_inc(x_170);
lean_dec(x_110);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_6);
return x_171;
}
}
case 8:
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_5, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_172, sizeof(void*)*1 + 4);
lean_dec(x_172);
x_174 = lean_ctor_get(x_6, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_box(x_173);
lean_inc(x_4);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_4);
x_178 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_175, x_177);
lean_dec(x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_179 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc_n(x_180, 2);
x_182 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(x_1, x_2, x_3, x_180, x_180, x_5, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 2);
lean_inc(x_184);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_182, 0);
x_187 = lean_ctor_get(x_182, 1);
lean_dec(x_187);
x_188 = !lean_is_exclusive(x_183);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_183, 2);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_184);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_184, 0);
x_192 = lean_box(x_173);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_180);
lean_inc(x_186);
x_194 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_191, x_193, x_186);
lean_ctor_set(x_184, 0, x_194);
return x_182;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_184, 0);
x_196 = lean_ctor_get(x_184, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_184);
x_197 = lean_box(x_173);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_180);
lean_inc(x_186);
x_199 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_195, x_198, x_186);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_196);
lean_ctor_set(x_183, 2, x_200);
return x_182;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_201 = lean_ctor_get(x_183, 0);
x_202 = lean_ctor_get(x_183, 1);
x_203 = lean_ctor_get(x_183, 3);
x_204 = lean_ctor_get(x_183, 4);
x_205 = lean_ctor_get(x_183, 5);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_183);
x_206 = lean_ctor_get(x_184, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_184, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_208 = x_184;
} else {
 lean_dec_ref(x_184);
 x_208 = lean_box(0);
}
x_209 = lean_box(x_173);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_180);
lean_inc(x_186);
x_211 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_206, x_210, x_186);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_207);
x_213 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_213, 0, x_201);
lean_ctor_set(x_213, 1, x_202);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_203);
lean_ctor_set(x_213, 4, x_204);
lean_ctor_set(x_213, 5, x_205);
lean_ctor_set(x_182, 1, x_213);
return x_182;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_214 = lean_ctor_get(x_182, 0);
lean_inc(x_214);
lean_dec(x_182);
x_215 = lean_ctor_get(x_183, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_183, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_183, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_183, 4);
lean_inc(x_218);
x_219 = lean_ctor_get(x_183, 5);
lean_inc(x_219);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 x_220 = x_183;
} else {
 lean_dec_ref(x_183);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_184, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_184, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_223 = x_184;
} else {
 lean_dec_ref(x_184);
 x_223 = lean_box(0);
}
x_224 = lean_box(x_173);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_180);
lean_inc(x_214);
x_226 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_221, x_225, x_214);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
if (lean_is_scalar(x_220)) {
 x_228 = lean_alloc_ctor(0, 6, 0);
} else {
 x_228 = x_220;
}
lean_ctor_set(x_228, 0, x_215);
lean_ctor_set(x_228, 1, x_216);
lean_ctor_set(x_228, 2, x_227);
lean_ctor_set(x_228, 3, x_217);
lean_ctor_set(x_228, 4, x_218);
lean_ctor_set(x_228, 5, x_219);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_214);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_180);
x_230 = !lean_is_exclusive(x_182);
if (x_230 == 0)
{
return x_182;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_182, 0);
x_232 = lean_ctor_get(x_182, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_182);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_179);
if (x_234 == 0)
{
return x_179;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_179, 0);
x_236 = lean_ctor_get(x_179, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_179);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_178, 0);
lean_inc(x_238);
lean_dec(x_178);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_6);
return x_239;
}
}
case 10:
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_4, 1);
lean_inc(x_240);
lean_dec(x_4);
x_4 = x_240;
goto _start;
}
case 11:
{
lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_242 = lean_ctor_get(x_5, 0);
lean_inc(x_242);
x_243 = lean_ctor_get_uint8(x_242, sizeof(void*)*1 + 4);
lean_dec(x_242);
x_244 = lean_ctor_get(x_6, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
x_246 = lean_box(x_243);
lean_inc(x_4);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_4);
x_248 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_20__getCachedWHNF___spec__1(x_245, x_247);
lean_dec(x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_249 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc_n(x_250, 2);
x_252 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__11(x_1, x_2, x_3, x_250, x_250, x_5, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
x_255 = !lean_is_exclusive(x_252);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_252, 0);
x_257 = lean_ctor_get(x_252, 1);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_253);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_253, 2);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_254);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_254, 0);
x_262 = lean_box(x_243);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_250);
lean_inc(x_256);
x_264 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_261, x_263, x_256);
lean_ctor_set(x_254, 0, x_264);
return x_252;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_254, 0);
x_266 = lean_ctor_get(x_254, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_254);
x_267 = lean_box(x_243);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_250);
lean_inc(x_256);
x_269 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_265, x_268, x_256);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_253, 2, x_270);
return x_252;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_271 = lean_ctor_get(x_253, 0);
x_272 = lean_ctor_get(x_253, 1);
x_273 = lean_ctor_get(x_253, 3);
x_274 = lean_ctor_get(x_253, 4);
x_275 = lean_ctor_get(x_253, 5);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_253);
x_276 = lean_ctor_get(x_254, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_254, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_278 = x_254;
} else {
 lean_dec_ref(x_254);
 x_278 = lean_box(0);
}
x_279 = lean_box(x_243);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_250);
lean_inc(x_256);
x_281 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_276, x_280, x_256);
if (lean_is_scalar(x_278)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_278;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_277);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_271);
lean_ctor_set(x_283, 1, x_272);
lean_ctor_set(x_283, 2, x_282);
lean_ctor_set(x_283, 3, x_273);
lean_ctor_set(x_283, 4, x_274);
lean_ctor_set(x_283, 5, x_275);
lean_ctor_set(x_252, 1, x_283);
return x_252;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_284 = lean_ctor_get(x_252, 0);
lean_inc(x_284);
lean_dec(x_252);
x_285 = lean_ctor_get(x_253, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_253, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_253, 3);
lean_inc(x_287);
x_288 = lean_ctor_get(x_253, 4);
lean_inc(x_288);
x_289 = lean_ctor_get(x_253, 5);
lean_inc(x_289);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 x_290 = x_253;
} else {
 lean_dec_ref(x_253);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_254, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_254, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_293 = x_254;
} else {
 lean_dec_ref(x_254);
 x_293 = lean_box(0);
}
x_294 = lean_box(x_243);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_250);
lean_inc(x_284);
x_296 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1(x_291, x_295, x_284);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_292);
if (lean_is_scalar(x_290)) {
 x_298 = lean_alloc_ctor(0, 6, 0);
} else {
 x_298 = x_290;
}
lean_ctor_set(x_298, 0, x_285);
lean_ctor_set(x_298, 1, x_286);
lean_ctor_set(x_298, 2, x_297);
lean_ctor_set(x_298, 3, x_287);
lean_ctor_set(x_298, 4, x_288);
lean_ctor_set(x_298, 5, x_289);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_284);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
else
{
uint8_t x_300; 
lean_dec(x_250);
x_300 = !lean_is_exclusive(x_252);
if (x_300 == 0)
{
return x_252;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_252, 0);
x_302 = lean_ctor_get(x_252, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_252);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_249);
if (x_304 == 0)
{
return x_249;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_249, 0);
x_306 = lean_ctor_get(x_249, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_249);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = lean_ctor_get(x_248, 0);
lean_inc(x_308);
lean_dec(x_248);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_6);
return x_309;
}
}
default: 
{
lean_object* x_310; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_4);
lean_ctor_set(x_310, 1, x_6);
return x_310;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_22__whnfAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_22__whnfAux___main___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_22__whnfAux___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceRec___at___private_Init_Lean_Meta_22__whnfAux___main___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__21___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isRecStuck___at___private_Init_Lean_Meta_22__whnfAux___main___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_22__whnfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_22__whnfAux___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_23__withCacheScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
lean_ctor_set(x_7, 2, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_ctor_get(x_7, 4);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_5, 1, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 5);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 6, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_4);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_27, 3);
x_33 = lean_ctor_get(x_27, 4);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_5, 1, x_35);
return x_5;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 5);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_44, 5, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_23__withCacheScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_23__withCacheScope___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 2);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_array_get_size(x_4);
lean_inc(x_4);
x_43 = lean_expr_instantiate_rev_range(x_40, x_5, x_42, x_4);
lean_dec(x_42);
lean_dec(x_40);
x_44 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_8);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_45);
x_47 = lean_local_ctx_mk_local_decl(x_3, x_45, x_38, x_43, x_39);
x_48 = lean_expr_mk_fvar(x_45);
x_49 = lean_array_push(x_4, x_48);
x_3 = x_47;
x_4 = x_49;
x_6 = x_41;
x_8 = x_46;
goto _start;
}
else
{
lean_object* x_51; 
x_51 = lean_box(0);
x_9 = x_51;
goto block_37;
}
block_37:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_10 = lean_array_get_size(x_4);
lean_inc(x_4);
x_11 = lean_expr_instantiate_rev_range(x_6, x_5, x_10, x_4);
lean_dec(x_5);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_11);
x_14 = lean_apply_3(x_1, x_11, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isForall(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_apply_4(x_2, x_4, x_11, x_7, x_16);
return x_18;
}
else
{
x_5 = x_10;
x_6 = x_11;
x_8 = x_16;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
lean_inc(x_3);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_1);
lean_inc(x_26);
lean_inc(x_11);
x_27 = lean_apply_3(x_1, x_11, x_26, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_isForall(x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_apply_4(x_2, x_4, x_11, x_26, x_29);
return x_31;
}
else
{
x_5 = x_10;
x_6 = x_11;
x_7 = x_26;
x_8 = x_29;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_24__forallTelescopeAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_24__forallTelescopeAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_6 = lean_apply_3(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_isForall(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = l_Array_empty___closed__1;
x_11 = lean_apply_4(x_3, x_10, x_2, x_4, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = l_Array_empty___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___rarg(x_1, x_3, x_13, x_14, x_15, x_7, x_4, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 2);
lean_dec(x_20);
lean_ctor_set(x_18, 2, x_12);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 3);
x_24 = lean_ctor_get(x_18, 4);
x_25 = lean_ctor_get(x_18, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_12);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_16, 1, x_26);
return x_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_12);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_16, 1);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 2);
lean_dec(x_40);
lean_ctor_set(x_38, 2, x_12);
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
x_43 = lean_ctor_get(x_38, 3);
x_44 = lean_ctor_get(x_38, 4);
x_45 = lean_ctor_get(x_38, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_12);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_16, 1, x_46);
return x_16;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_16, 1);
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 5);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_12);
lean_ctor_set(x_55, 3, x_51);
lean_ctor_set(x_55, 4, x_52);
lean_ctor_set(x_55, 5, x_53);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isClassQuickConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_is_class(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_17__getConst(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lean_box(2);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(2);
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
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
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
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
lean_object* l_Lean_Meta_isClassQuickConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isClassQuickConst(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_get_expr_assignment(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_1 = x_9;
goto _start;
}
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_isClassQuickConst(x_11, x_2, x_3);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Expr_getAppFn___main(x_13);
lean_dec(x_13);
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_isClassQuickConst(x_15, x_2, x_3);
return x_16;
}
case 6:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
case 7:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_1 = x_21;
goto _start;
}
case 8:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
case 10:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
case 11:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_25__isClassQuick___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_25__isClassQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_25__isClassQuick___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_25__isClassQuick___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_25__isClassQuick(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_26__isClassExpensive___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_70 = lean_ctor_get(x_5, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 2);
lean_inc(x_71);
lean_dec(x_5);
x_72 = lean_array_get_size(x_3);
lean_inc(x_3);
x_73 = lean_expr_instantiate_rev_range(x_70, x_4, x_72, x_3);
lean_dec(x_72);
lean_dec(x_70);
x_74 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_7);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_75);
x_77 = lean_local_ctx_mk_local_decl(x_2, x_75, x_68, x_73, x_69);
x_78 = lean_expr_mk_fvar(x_75);
x_79 = lean_array_push(x_3, x_78);
x_2 = x_77;
x_3 = x_79;
x_5 = x_71;
x_7 = x_76;
goto _start;
}
else
{
lean_object* x_81; 
x_81 = lean_box(0);
x_8 = x_81;
goto block_67;
}
block_67:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_8);
x_9 = lean_array_get_size(x_3);
lean_inc(x_3);
x_10 = lean_expr_instantiate_rev_range(x_5, x_4, x_9, x_3);
lean_dec(x_4);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_10);
x_13 = lean_apply_3(x_1, x_10, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_isForall(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Expr_getAppFn___main(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_inc(x_19);
x_21 = lean_is_class(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
else
{
lean_object* x_24; 
lean_dec(x_18);
x_24 = lean_box(0);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_free_object(x_13);
x_4 = x_9;
x_5 = x_10;
x_7 = x_16;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = l_Lean_Expr_isForall(x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Expr_getAppFn___main(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_inc(x_30);
x_32 = lean_is_class(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
}
else
{
x_4 = x_9;
x_5 = x_10;
x_7 = x_27;
goto _start;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_1);
lean_inc(x_46);
lean_inc(x_10);
x_47 = lean_apply_3(x_1, x_10, x_46, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
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
x_51 = l_Lean_Expr_isForall(x_48);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = l_Lean_Expr_getAppFn___main(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_52) == 4)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_inc(x_53);
x_55 = lean_is_class(x_54, x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
x_56 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
if (lean_is_scalar(x_50)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_50;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_52);
x_60 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_50;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
}
else
{
lean_dec(x_50);
x_4 = x_9;
x_5 = x_10;
x_6 = x_46;
x_7 = x_49;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_65 = x_47;
} else {
 lean_dec_ref(x_47);
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
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_26__isClassExpensive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_isForall(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_10 = l_Lean_Expr_getAppFn___main(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_is_class(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_box(0);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
lean_dec(x_2);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = l_Array_empty___closed__1;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_26__isClassExpensive___spec__2(x_1, x_18, x_19, x_20, x_7, x_3, x_8);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 2);
lean_dec(x_25);
lean_ctor_set(x_23, 2, x_17);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 3);
x_29 = lean_ctor_get(x_23, 4);
x_30 = lean_ctor_get(x_23, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_21, 1, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 6, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_21, 1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 2);
lean_dec(x_45);
lean_ctor_set(x_43, 2, x_17);
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_43, 3);
x_49 = lean_ctor_get(x_43, 4);
x_50 = lean_ctor_get(x_43, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_17);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_49);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_21, 1, x_51);
return x_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_21, 1);
x_53 = lean_ctor_get(x_21, 0);
lean_inc(x_52);
lean_inc(x_53);
lean_dec(x_21);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_17);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_5, 0);
x_63 = lean_ctor_get(x_5, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_5);
x_64 = l_Lean_Expr_isForall(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_1);
x_65 = l_Lean_Expr_getAppFn___main(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_65) == 4)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_inc(x_66);
x_68 = lean_is_class(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_66);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_63);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
x_75 = lean_ctor_get(x_63, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
x_77 = l_Array_empty___closed__1;
x_78 = lean_unsigned_to_nat(0u);
x_79 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_26__isClassExpensive___spec__2(x_1, x_76, x_77, x_78, x_62, x_3, x_63);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_75);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_93 = x_79;
} else {
 lean_dec_ref(x_79);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 5);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_75);
lean_ctor_set(x_100, 3, x_96);
lean_ctor_set(x_100, 4, x_97);
lean_ctor_set(x_100, 5, x_98);
if (lean_is_scalar(x_93)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_93;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_5);
if (x_102 == 0)
{
return x_5;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_5, 0);
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_5);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_26__isClassExpensive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_26__isClassExpensive___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l___private_Init_Lean_Meta_25__isClassQuick___main(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
case 1:
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_26__isClassExpensive___spec__1(x_1, x_2, x_3, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_22 = lean_nat_sub(x_4, x_12);
x_23 = lean_nat_sub(x_22, x_11);
lean_dec(x_22);
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_26 = x_6;
} else {
 lean_dec_ref(x_6);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_23);
x_59 = lean_ctor_get(x_25, 2);
lean_inc(x_59);
lean_dec(x_25);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_8);
x_13 = x_61;
goto block_21;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_58;
}
block_21:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_5 = x_12;
x_6 = x_14;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
block_58:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_27);
lean_inc(x_3);
x_28 = lean_expr_instantiate_rev_range(x_25, x_24, x_23, x_3);
lean_dec(x_24);
lean_dec(x_25);
lean_inc(x_1);
lean_inc(x_7);
x_29 = lean_apply_3(x_1, x_28, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 7)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
lean_dec(x_30);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_29, 0, x_34);
x_13 = x_29;
goto block_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 2);
lean_inc(x_36);
lean_dec(x_30);
if (lean_is_scalar(x_26)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_26;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_13 = x_38;
goto block_21;
}
}
else
{
uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_29, 1);
x_41 = lean_ctor_get(x_29, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_3);
lean_inc(x_2);
x_46 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_3);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_46);
x_13 = x_29;
goto block_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_dec(x_29);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_3);
lean_inc(x_2);
x_52 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
x_13 = x_53;
goto block_21;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_23);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
x_13 = x_29;
goto block_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_13 = x_57;
goto block_21;
}
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_8);
return x_63;
}
}
}
lean_object* l___private_Init_Lean_Meta_27__getForallResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_array_get_size(x_3);
lean_inc(x_8);
lean_inc(x_3);
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1(x_1, x_2, x_3, x_8, x_8, x_7, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_instantiate_rev_range(x_13, x_12, x_8, x_3);
lean_dec(x_8);
lean_dec(x_12);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_expr_instantiate_rev_range(x_18, x_17, x_8, x_3);
lean_dec(x_8);
lean_dec(x_17);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_3);
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
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_27__getForallResultType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_28__inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = lean_apply_3(x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_8, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* l___private_Init_Lean_Meta_29__inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_ConstantInfo_lparams(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_List_lengthAux___main___rarg(x_13, x_14);
lean_dec(x_13);
x_16 = l_List_lengthAux___main___rarg(x_2, x_14);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_instantiate_type_lparams(x_12, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_29__inferConstType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_29__inferConstType(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_8);
x_16 = lean_apply_3(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_hasLooseBVars(x_19);
if (x_20 == 0)
{
lean_dec(x_15);
x_6 = x_13;
x_7 = x_19;
x_9 = x_18;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_4);
lean_inc(x_2);
x_22 = lean_expr_mk_proj(x_2, x_15, x_4);
x_23 = lean_expr_instantiate1(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_6 = x_13;
x_7 = x_23;
x_9 = x_18;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
}
}
lean_object* l___private_Init_Lean_Meta_30__inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_3(x_1, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_getAppFn___main(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = lean_environment_find(x_15, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_5);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_14, x_33);
x_35 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_14, x_36, x_38);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_eq(x_31, x_40);
lean_dec(x_40);
lean_dec(x_31);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_1);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_44);
return x_11;
}
else
{
lean_object* x_45; 
lean_inc(x_15);
x_45 = lean_environment_find(x_15, x_32);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_19);
lean_dec(x_1);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_dec(x_6);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_16);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_4);
lean_ctor_set(x_48, 2, x_5);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_48);
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_11);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_instantiate_type_lparams(x_49, x_19);
lean_inc(x_6);
lean_inc(x_1);
x_51 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_50, x_39, x_6, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_n(x_4, 2);
lean_inc(x_3);
lean_inc(x_1);
x_54 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1(x_1, x_3, x_4, x_5, x_4, x_4, x_52, x_6, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_6);
x_57 = lean_apply_3(x_1, x_55, x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 7)
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_58);
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_57, 1);
x_67 = lean_ctor_get(x_57, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_6, 1);
lean_inc(x_70);
lean_dec(x_6);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_4);
lean_ctor_set(x_72, 2, x_5);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_72);
return x_57;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_57, 1);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_6, 1);
lean_inc(x_76);
lean_dec(x_6);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_4);
lean_ctor_set(x_78, 2, x_5);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_57);
if (x_80 == 0)
{
return x_57;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_57, 0);
x_82 = lean_ctor_get(x_57, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_57);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_54);
if (x_84 == 0)
{
return x_54;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_54, 0);
x_86 = lean_ctor_get(x_54, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_54);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_51);
if (x_88 == 0)
{
return x_51;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_51, 0);
x_90 = lean_ctor_get(x_51, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_51);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_92 = lean_ctor_get(x_6, 1);
lean_inc(x_92);
lean_dec(x_6);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_15);
lean_ctor_set(x_93, 1, x_16);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_94, 0, x_3);
lean_ctor_set(x_94, 1, x_4);
lean_ctor_set(x_94, 2, x_5);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_94);
return x_11;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
lean_dec(x_6);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_15);
lean_ctor_set(x_96, 1, x_16);
lean_ctor_set(x_96, 2, x_95);
x_97 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_97, 0, x_3);
lean_ctor_set(x_97, 1, x_4);
lean_ctor_set(x_97, 2, x_5);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_97);
return x_11;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_1);
x_98 = lean_ctor_get(x_6, 1);
lean_inc(x_98);
lean_dec(x_6);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_15);
lean_ctor_set(x_99, 1, x_16);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_100, 0, x_3);
lean_ctor_set(x_100, 1, x_4);
lean_ctor_set(x_100, 2, x_5);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_100);
return x_11;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_11, 1);
x_102 = lean_ctor_get(x_11, 0);
lean_inc(x_101);
lean_inc(x_102);
lean_dec(x_11);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
x_105 = l_Lean_Expr_getAppFn___main(x_102);
if (lean_obj_tag(x_105) == 4)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_103);
x_108 = lean_environment_find(x_103, x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_1);
x_109 = lean_ctor_get(x_6, 1);
lean_inc(x_109);
lean_dec(x_6);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_109);
x_111 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_4);
lean_ctor_set(x_111, 2, x_5);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_101);
return x_112;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
lean_dec(x_108);
if (lean_obj_tag(x_113) == 5)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_ctor_get(x_114, 4);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_1);
x_116 = lean_ctor_get(x_6, 1);
lean_inc(x_116);
lean_dec(x_6);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_118, 0, x_3);
lean_ctor_set(x_118, 1, x_4);
lean_ctor_set(x_118, 2, x_5);
lean_ctor_set(x_118, 3, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_101);
return x_119;
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_dec(x_114);
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
lean_dec(x_115);
x_123 = lean_unsigned_to_nat(0u);
x_124 = l_Lean_Expr_getAppNumArgsAux___main(x_102, x_123);
x_125 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_124);
x_126 = lean_mk_array(x_124, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_124, x_127);
lean_dec(x_124);
x_129 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_102, x_126, x_128);
x_130 = lean_array_get_size(x_129);
x_131 = lean_nat_dec_eq(x_121, x_130);
lean_dec(x_130);
lean_dec(x_121);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_129);
lean_dec(x_122);
lean_dec(x_107);
lean_dec(x_1);
x_132 = lean_ctor_get(x_6, 1);
lean_inc(x_132);
lean_dec(x_6);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_103);
lean_ctor_set(x_133, 1, x_104);
lean_ctor_set(x_133, 2, x_132);
x_134 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_134, 0, x_3);
lean_ctor_set(x_134, 1, x_4);
lean_ctor_set(x_134, 2, x_5);
lean_ctor_set(x_134, 3, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_101);
return x_135;
}
else
{
lean_object* x_136; 
lean_inc(x_103);
x_136 = lean_environment_find(x_103, x_122);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_129);
lean_dec(x_107);
lean_dec(x_1);
x_137 = lean_ctor_get(x_6, 1);
lean_inc(x_137);
lean_dec(x_6);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_103);
lean_ctor_set(x_138, 1, x_104);
lean_ctor_set(x_138, 2, x_137);
x_139 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_139, 0, x_3);
lean_ctor_set(x_139, 1, x_4);
lean_ctor_set(x_139, 2, x_5);
lean_ctor_set(x_139, 3, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_101);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_104);
lean_dec(x_103);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_instantiate_type_lparams(x_141, x_107);
lean_inc(x_6);
lean_inc(x_1);
x_143 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_142, x_129, x_6, x_101);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_n(x_4, 2);
lean_inc(x_3);
lean_inc(x_1);
x_146 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1(x_1, x_3, x_4, x_5, x_4, x_4, x_144, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_6);
x_149 = lean_apply_3(x_1, x_147, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 7)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_150);
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_6, 1);
lean_inc(x_159);
lean_dec(x_6);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_161, 0, x_3);
lean_ctor_set(x_161, 1, x_4);
lean_ctor_set(x_161, 2, x_5);
lean_ctor_set(x_161, 3, x_160);
if (lean_is_scalar(x_156)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_156;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_155);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = lean_ctor_get(x_149, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
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
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = lean_ctor_get(x_146, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_146, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_169 = x_146;
} else {
 lean_dec_ref(x_146);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_171 = lean_ctor_get(x_143, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_143, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_173 = x_143;
} else {
 lean_dec_ref(x_143);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_1);
x_175 = lean_ctor_get(x_6, 1);
lean_inc(x_175);
lean_dec(x_6);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_103);
lean_ctor_set(x_176, 1, x_104);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
lean_ctor_set(x_177, 2, x_5);
lean_ctor_set(x_177, 3, x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_101);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_113);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_1);
x_179 = lean_ctor_get(x_6, 1);
lean_inc(x_179);
lean_dec(x_6);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_103);
lean_ctor_set(x_180, 1, x_104);
lean_ctor_set(x_180, 2, x_179);
x_181 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_181, 0, x_3);
lean_ctor_set(x_181, 1, x_4);
lean_ctor_set(x_181, 2, x_5);
lean_ctor_set(x_181, 3, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_101);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_1);
x_183 = lean_ctor_get(x_6, 1);
lean_inc(x_183);
lean_dec(x_6);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_103);
lean_ctor_set(x_184, 1, x_104);
lean_ctor_set(x_184, 2, x_183);
x_185 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_185, 0, x_3);
lean_ctor_set(x_185, 1, x_4);
lean_ctor_set(x_185, 2, x_5);
lean_ctor_set(x_185, 3, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_101);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_11);
if (x_187 == 0)
{
return x_11;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_11, 0);
x_189 = lean_ctor_get(x_11, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_8);
if (x_191 == 0)
{
return x_8;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_8, 0);
x_193 = lean_ctor_get(x_8, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_8);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_30__inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_31__getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_3(x_1, x_3, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_11);
x_12 = l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(x_11, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_level_mk_mvar(x_17);
lean_inc(x_19);
x_20 = lean_expr_mk_sort(x_19);
x_21 = l___private_Init_Lean_Meta_15__assignExprMVar(x_11, x_20, x_4, x_18);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
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
else
{
uint8_t x_30; 
lean_dec(x_11);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_12, 1);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
return x_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 3:
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_8, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
default: 
{
uint8_t x_55; 
lean_dec(x_9);
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_8, 1);
x_57 = lean_ctor_get(x_8, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_dec(x_4);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_62);
return x_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_dec(x_8);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_dec(x_4);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_8);
if (x_70 == 0)
{
return x_8;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_8, 0);
x_72 = lean_ctor_get(x_8, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_8);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_6);
if (x_74 == 0)
{
return x_6;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_6, 0);
x_76 = lean_ctor_get(x_6, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_6);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_2);
lean_inc(x_8);
x_15 = lean_apply_3(x_2, x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Meta_31__getLevel(x_1, x_2, x_16, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_level_mk_imax(x_19, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_21;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_86 = lean_ctor_get(x_6, 0);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_88 = lean_ctor_get(x_6, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_6, 2);
lean_inc(x_89);
lean_dec(x_6);
x_90 = lean_array_get_size(x_4);
lean_inc(x_4);
x_91 = lean_expr_instantiate_rev_range(x_88, x_5, x_90, x_4);
lean_dec(x_90);
lean_dec(x_88);
x_92 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_8);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_93);
x_95 = lean_local_ctx_mk_local_decl(x_3, x_93, x_86, x_91, x_87);
x_96 = lean_expr_mk_fvar(x_93);
x_97 = lean_array_push(x_4, x_96);
x_3 = x_95;
x_4 = x_97;
x_6 = x_89;
x_8 = x_94;
goto _start;
}
else
{
lean_object* x_99; 
x_99 = lean_box(0);
x_9 = x_99;
goto block_85;
}
block_85:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_10 = lean_array_get_size(x_4);
lean_inc(x_4);
x_11 = lean_expr_instantiate_rev_range(x_6, x_5, x_10, x_4);
lean_dec(x_5);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_11);
x_14 = lean_apply_3(x_1, x_11, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isForall(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_7);
x_18 = lean_apply_3(x_2, x_11, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Init_Lean_Meta_31__getLevel(x_1, x_2, x_19, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(x_1, x_2, x_4, x_4, x_10, lean_box(0), x_22, x_7, x_23);
lean_dec(x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_expr_mk_sort(x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_expr_mk_sort(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
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
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
x_5 = x_10;
x_6 = x_11;
x_8 = x_16;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
lean_inc(x_3);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_1);
lean_inc(x_51);
lean_inc(x_11);
x_52 = lean_apply_3(x_1, x_11, x_51, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_isForall(x_53);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_56 = lean_apply_3(x_2, x_11, x_51, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_51);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Init_Lean_Meta_31__getLevel(x_1, x_2, x_57, x_51, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(x_1, x_2, x_4, x_4, x_10, lean_box(0), x_60, x_51, x_61);
lean_dec(x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
x_66 = lean_expr_mk_sort(x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
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
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_56, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_78 = x_56;
} else {
 lean_dec_ref(x_56);
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
x_5 = x_10;
x_6 = x_11;
x_7 = x_51;
x_8 = x_54;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_52, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_83 = x_52;
} else {
 lean_dec_ref(x_52);
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
}
lean_object* _init_l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_isForall(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Init_Lean_Meta_31__getLevel(x_1, x_2, x_11, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty___closed__1;
x_17 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1;
x_18 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(x_1, x_2, x_16, x_16, x_17, lean_box(0), x_14, x_4, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_expr_mk_sort(x_20);
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
x_24 = lean_expr_mk_sort(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
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
lean_dec(x_4);
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
lean_dec(x_4);
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
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_38 = lean_ctor_get(x_8, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = l_Array_empty___closed__1;
x_41 = lean_unsigned_to_nat(0u);
x_42 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__3(x_1, x_2, x_39, x_40, x_41, x_7, x_4, x_8);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 1);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 2);
lean_dec(x_46);
lean_ctor_set(x_44, 2, x_38);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_ctor_get(x_44, 3);
x_50 = lean_ctor_get(x_44, 4);
x_51 = lean_ctor_get(x_44, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_38);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_42, 1, x_52);
return x_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_42, 1);
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 5);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 6, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_38);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set(x_61, 4, x_58);
lean_ctor_set(x_61, 5, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_42);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_42, 1);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 2);
lean_dec(x_66);
lean_ctor_set(x_64, 2, x_38);
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_64, 3);
x_70 = lean_ctor_get(x_64, 4);
x_71 = lean_ctor_get(x_64, 5);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_42, 1, x_72);
return x_42;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_42, 1);
x_74 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
lean_inc(x_74);
lean_dec(x_42);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 5);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 6, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_38);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_6);
if (x_83 == 0)
{
return x_6;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_6, 0);
x_85 = lean_ctor_get(x_6, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_6);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_32__inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_32__inferForallType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_expr_mk_fvar(x_9);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_local_ctx_mk_local_decl(x_13, x_9, x_1, x_3, x_2);
lean_ctor_set(x_5, 1, x_14);
x_15 = lean_apply_3(x_4, x_11, x_5, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 2);
lean_dec(x_19);
lean_ctor_set(x_17, 2, x_7);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_15, 1, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_7);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_15, 1);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 2);
lean_dec(x_39);
lean_ctor_set(x_37, 2, x_7);
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 3);
x_43 = lean_ctor_get(x_37, 4);
x_44 = lean_ctor_get(x_37, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_7);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_15, 1, x_45);
return x_15;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_15, 1);
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_7);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_51);
lean_ctor_set(x_54, 5, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = lean_ctor_get(x_5, 1);
x_58 = lean_ctor_get(x_5, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_5);
x_59 = lean_local_ctx_mk_local_decl(x_57, x_9, x_1, x_3, x_2);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = lean_apply_3(x_4, x_11, x_60, x_10);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 6, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_7);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 5);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_77);
lean_ctor_set(x_82, 2, x_7);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_80);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_33__withLocalDecl___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_33__withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Lean_Meta_33__withLocalDecl___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_34__inferMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_find_decl(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Meta_34__inferMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_34__inferMVarType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_35__inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_5 = lean_local_ctx_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
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
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_expr_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
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
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
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
x_58 = lean_box(2);
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
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_71, x_73, x_74, x_4, x_5);
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
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__6(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_expr_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_expr_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Meta_36__checkInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 2);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_18 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_17, x_1, x_12);
lean_ctor_set(x_10, 1, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_12);
x_21 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_20, x_1, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_9, 2, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 3);
x_26 = lean_ctor_get(x_9, 4);
x_27 = lean_ctor_get(x_9, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_30 = x_10;
} else {
 lean_dec_ref(x_10);
 x_30 = lean_box(0);
}
lean_inc(x_12);
x_31 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_29, x_1, x_12);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set(x_33, 4, x_26);
lean_ctor_set(x_33, 5, x_27);
lean_ctor_set(x_8, 1, x_33);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_40 = x_9;
} else {
 lean_dec_ref(x_9);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_43 = x_10;
} else {
 lean_dec_ref(x_10);
 x_43 = lean_box(0);
}
lean_inc(x_34);
x_44 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_42, x_1, x_34);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 6, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_38);
lean_ctor_set(x_46, 5, x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_7, 0);
lean_inc(x_52);
lean_dec(x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_inhabited___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_panicWithPos___rarg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_panicWithPos___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_panicWithPos___rarg___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_panicWithPos___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_4);
x_20 = l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l___private_Init_Lean_Meta_28__inferAppType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_7, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_10);
x_11 = l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(x_10, x_3, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_level_mk_mvar(x_16);
lean_inc(x_18);
x_19 = lean_expr_mk_sort(x_18);
x_20 = l___private_Init_Lean_Meta_15__assignExprMVar(x_10, x_19, x_3, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
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
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_36);
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 3:
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_7, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_dec(x_7);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
default: 
{
uint8_t x_54; 
lean_dec(x_8);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_7, 1);
x_56 = lean_ctor_get(x_7, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
return x_5;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_10);
x_11 = l___private_Init_Lean_Meta_12__isReadOnlyOrSyntheticMVar(x_10, x_3, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_level_mk_mvar(x_16);
lean_inc(x_18);
x_19 = lean_expr_mk_sort(x_18);
x_20 = l___private_Init_Lean_Meta_15__assignExprMVar(x_10, x_19, x_3, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
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
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_36);
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 3:
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_7, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_dec(x_7);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
default: 
{
uint8_t x_54; 
lean_dec(x_8);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_7, 1);
x_56 = lean_ctor_get(x_7, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
return x_5;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_array_fget(x_3, x_12);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__5(x_1, x_15, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_level_mk_imax(x_18, x_6);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_20;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
}
}
lean_object* l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_5, 2);
lean_inc(x_88);
lean_dec(x_5);
x_89 = lean_array_get_size(x_3);
lean_inc(x_3);
x_90 = lean_expr_instantiate_rev_range(x_87, x_4, x_89, x_3);
lean_dec(x_89);
lean_dec(x_87);
x_91 = l___private_Init_Lean_Meta_7__mkFreshId___rarg(x_7);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_92);
x_94 = lean_local_ctx_mk_local_decl(x_2, x_92, x_85, x_90, x_86);
x_95 = lean_expr_mk_fvar(x_92);
x_96 = lean_array_push(x_3, x_95);
x_2 = x_94;
x_3 = x_96;
x_5 = x_88;
x_7 = x_93;
goto _start;
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_8 = x_98;
goto block_84;
}
block_84:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_8);
x_9 = lean_array_get_size(x_3);
lean_inc(x_3);
x_10 = lean_expr_instantiate_rev_range(x_5, x_4, x_9, x_3);
lean_dec(x_4);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_10);
x_13 = lean_apply_3(x_1, x_10, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_isForall(x_14);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_10, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__4(x_1, x_18, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(x_1, x_3, x_3, x_9, lean_box(0), x_21, x_6, x_22);
lean_dec(x_3);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_expr_mk_sort(x_25);
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
x_29 = lean_expr_mk_sort(x_27);
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
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_9);
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
x_4 = x_9;
x_5 = x_10;
x_7 = x_15;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_49);
lean_inc(x_1);
lean_inc(x_50);
lean_inc(x_10);
x_51 = lean_apply_3(x_1, x_10, x_50, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Expr_isForall(x_52);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_2);
lean_inc(x_50);
lean_inc(x_1);
x_55 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_10, x_50, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_50);
lean_inc(x_1);
x_58 = l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__4(x_1, x_56, x_50, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(x_1, x_3, x_3, x_9, lean_box(0), x_59, x_50, x_60);
lean_dec(x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_expr_mk_sort(x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_dec(x_50);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_50);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_ctor_get(x_55, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_77 = x_55;
} else {
 lean_dec_ref(x_55);
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
x_4 = x_9;
x_5 = x_10;
x_6 = x_50;
x_7 = x_53;
goto _start;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_51, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_51, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_82 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_object* l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Expr_isForall(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Init_Lean_Meta_31__getLevel___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__4(x_1, x_10, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_empty___closed__1;
x_16 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1;
x_17 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(x_1, x_15, x_15, x_16, lean_box(0), x_13, x_3, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_expr_mk_sort(x_19);
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
x_23 = lean_expr_mk_sort(x_21);
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
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
x_39 = l_Array_empty___closed__1;
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Init_Lean_Meta_24__forallTelescopeAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__8(x_1, x_38, x_39, x_40, x_6, x_3, x_7);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 2);
lean_dec(x_45);
lean_ctor_set(x_43, 2, x_37);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_43, 3);
x_49 = lean_ctor_get(x_43, 4);
x_50 = lean_ctor_get(x_43, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_49);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_41, 1, x_51);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_41, 1);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_37);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_41, 1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 2);
lean_dec(x_65);
lean_ctor_set(x_63, 2, x_37);
return x_41;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = lean_ctor_get(x_63, 3);
x_69 = lean_ctor_get(x_63, 4);
x_70 = lean_ctor_get(x_63, 5);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_37);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_41, 1, x_71);
return x_41;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_41, 1);
x_73 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_37);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_77);
lean_ctor_set(x_80, 5, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_5);
if (x_82 == 0)
{
return x_5;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_32__inferForallType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__7(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_8);
x_16 = lean_apply_3(x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_hasLooseBVars(x_19);
if (x_20 == 0)
{
lean_dec(x_15);
x_6 = x_13;
x_7 = x_19;
x_9 = x_18;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_4);
lean_inc(x_2);
x_22 = lean_expr_mk_proj(x_2, x_15, x_4);
x_23 = lean_expr_instantiate1(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_6 = x_13;
x_7 = x_23;
x_9 = x_18;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
}
}
lean_object* l___private_Init_Lean_Meta_30__inferProjType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_5);
x_10 = lean_apply_3(x_1, x_8, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = l_Lean_Expr_getAppFn___main(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = lean_environment_find(x_14, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_32);
x_34 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_33);
x_35 = lean_mk_array(x_33, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_33, x_36);
lean_dec(x_33);
x_38 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_13, x_35, x_37);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_eq(x_30, x_39);
lean_dec(x_39);
lean_dec(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_1);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_15);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_3);
lean_ctor_set(x_43, 2, x_4);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_43);
return x_10;
}
else
{
lean_object* x_44; 
lean_inc(x_14);
x_44 = lean_environment_find(x_14, x_31);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
lean_dec(x_18);
lean_dec(x_1);
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_15);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_3);
lean_ctor_set(x_47, 2, x_4);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_47);
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_10);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_instantiate_type_lparams(x_48, x_18);
lean_inc(x_5);
lean_inc(x_1);
x_50 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_49, x_38, x_5, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_n(x_3, 2);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10(x_1, x_2, x_3, x_4, x_3, x_3, x_51, x_5, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_5);
x_56 = lean_apply_3(x_1, x_54, x_5, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 7)
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_57);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_56, 1);
x_66 = lean_ctor_get(x_56, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_3);
lean_ctor_set(x_71, 2, x_4);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_71);
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_dec(x_5);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
x_77 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_77, 2, x_4);
lean_ctor_set(x_77, 3, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_50);
if (x_87 == 0)
{
return x_50;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_50, 0);
x_89 = lean_ctor_get(x_50, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_50);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
lean_dec(x_5);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_14);
lean_ctor_set(x_92, 1, x_15);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_4);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_93);
return x_10;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
lean_dec(x_5);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_14);
lean_ctor_set(x_95, 1, x_15);
lean_ctor_set(x_95, 2, x_94);
x_96 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_3);
lean_ctor_set(x_96, 2, x_4);
lean_ctor_set(x_96, 3, x_95);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_96);
return x_10;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_1);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
lean_dec(x_5);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_14);
lean_ctor_set(x_98, 1, x_15);
lean_ctor_set(x_98, 2, x_97);
x_99 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_4);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_99);
return x_10;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_10, 1);
x_101 = lean_ctor_get(x_10, 0);
lean_inc(x_100);
lean_inc(x_101);
lean_dec(x_10);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
x_104 = l_Lean_Expr_getAppFn___main(x_101);
if (lean_obj_tag(x_104) == 4)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_102);
x_107 = lean_environment_find(x_102, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_1);
x_108 = lean_ctor_get(x_5, 1);
lean_inc(x_108);
lean_dec(x_5);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set(x_110, 3, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_100);
return x_111;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
if (lean_obj_tag(x_112) == 5)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_113, 4);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_113);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_1);
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_dec(x_5);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_103);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_117, 0, x_2);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 2, x_4);
lean_ctor_set(x_117, 3, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_100);
return x_118;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
lean_dec(x_113);
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
lean_dec(x_114);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Expr_getAppNumArgsAux___main(x_101, x_122);
x_124 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_123);
x_125 = lean_mk_array(x_123, x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_123, x_126);
lean_dec(x_123);
x_128 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_101, x_125, x_127);
x_129 = lean_array_get_size(x_128);
x_130 = lean_nat_dec_eq(x_120, x_129);
lean_dec(x_129);
lean_dec(x_120);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_128);
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_1);
x_131 = lean_ctor_get(x_5, 1);
lean_inc(x_131);
lean_dec(x_5);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_102);
lean_ctor_set(x_132, 1, x_103);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_133, 0, x_2);
lean_ctor_set(x_133, 1, x_3);
lean_ctor_set(x_133, 2, x_4);
lean_ctor_set(x_133, 3, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_100);
return x_134;
}
else
{
lean_object* x_135; 
lean_inc(x_102);
x_135 = lean_environment_find(x_102, x_121);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_128);
lean_dec(x_106);
lean_dec(x_1);
x_136 = lean_ctor_get(x_5, 1);
lean_inc(x_136);
lean_dec(x_5);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_102);
lean_ctor_set(x_137, 1, x_103);
lean_ctor_set(x_137, 2, x_136);
x_138 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_3);
lean_ctor_set(x_138, 2, x_4);
lean_ctor_set(x_138, 3, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_100);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_103);
lean_dec(x_102);
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
lean_dec(x_135);
x_141 = lean_instantiate_type_lparams(x_140, x_106);
lean_inc(x_5);
lean_inc(x_1);
x_142 = l___private_Init_Lean_Meta_27__getForallResultType(x_1, x_141, x_128, x_5, x_100);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_n(x_3, 2);
lean_inc(x_2);
lean_inc(x_1);
x_145 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10(x_1, x_2, x_3, x_4, x_3, x_3, x_143, x_5, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_5);
x_148 = lean_apply_3(x_1, x_146, x_5, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 7)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_149);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_155 = x_148;
} else {
 lean_dec_ref(x_148);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_5, 1);
lean_inc(x_158);
lean_dec(x_5);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_160, 0, x_2);
lean_ctor_set(x_160, 1, x_3);
lean_ctor_set(x_160, 2, x_4);
lean_ctor_set(x_160, 3, x_159);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_155;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_154);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_ctor_get(x_148, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_148, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_164 = x_148;
} else {
 lean_dec_ref(x_148);
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
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_145, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_145, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_168 = x_145;
} else {
 lean_dec_ref(x_145);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_142, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_142, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_172 = x_142;
} else {
 lean_dec_ref(x_142);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_119);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_1);
x_174 = lean_ctor_get(x_5, 1);
lean_inc(x_174);
lean_dec(x_5);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_102);
lean_ctor_set(x_175, 1, x_103);
lean_ctor_set(x_175, 2, x_174);
x_176 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_176, 0, x_2);
lean_ctor_set(x_176, 1, x_3);
lean_ctor_set(x_176, 2, x_4);
lean_ctor_set(x_176, 3, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_100);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_112);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_1);
x_178 = lean_ctor_get(x_5, 1);
lean_inc(x_178);
lean_dec(x_5);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_102);
lean_ctor_set(x_179, 1, x_103);
lean_ctor_set(x_179, 2, x_178);
x_180 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_180, 0, x_2);
lean_ctor_set(x_180, 1, x_3);
lean_ctor_set(x_180, 2, x_4);
lean_ctor_set(x_180, 3, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_100);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_1);
x_182 = lean_ctor_get(x_5, 1);
lean_inc(x_182);
lean_dec(x_5);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_102);
lean_ctor_set(x_183, 1, x_103);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_184, 0, x_2);
lean_ctor_set(x_184, 1, x_3);
lean_ctor_set(x_184, 2, x_4);
lean_ctor_set(x_184, 3, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_100);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_10);
if (x_186 == 0)
{
return x_10;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_10, 0);
x_188 = lean_ctor_get(x_10, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_10);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_7);
if (x_190 == 0)
{
return x_7;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_7, 0);
x_192 = lean_ctor_get(x_7, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_7);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implemented yet");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_unreachable_x21___rarg___closed__1;
x_6 = lean_unsigned_to_nat(37u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_unreachable_x21___rarg___closed__2;
x_9 = l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1(x_5, x_6, x_7, x_8, x_3, x_4);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l___private_Init_Lean_Meta_35__inferFVarType(x_10, x_3, x_4);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___private_Init_Lean_Meta_34__inferMVarType(x_12, x_3, x_4);
lean_dec(x_3);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_level_mk_succ(x_14);
x_16 = lean_expr_mk_sort(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l___private_Init_Lean_Meta_29__inferConstType(x_18, x_19, x_3, x_4);
lean_dec(x_3);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_22);
x_24 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
lean_inc(x_2);
x_28 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_25, x_27);
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(x_30, x_2);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l___private_Init_Lean_Meta_28__inferAppType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__2(x_1, x_21, x_28, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_33, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_42 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_41, x_2, x_36);
lean_ctor_set(x_34, 1, x_42);
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
lean_inc(x_36);
x_45 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_44, x_2, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_33, 2, x_46);
return x_32;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
x_49 = lean_ctor_get(x_33, 3);
x_50 = lean_ctor_get(x_33, 4);
x_51 = lean_ctor_get(x_33, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_54 = x_34;
} else {
 lean_dec_ref(x_34);
 x_54 = lean_box(0);
}
lean_inc(x_36);
x_55 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_53, x_2, x_36);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
lean_ctor_set(x_57, 5, x_51);
lean_ctor_set(x_32, 1, x_57);
return x_32;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
lean_dec(x_32);
x_59 = lean_ctor_get(x_33, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_33, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_33, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_33, 5);
lean_inc(x_63);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 lean_ctor_release(x_33, 4);
 lean_ctor_release(x_33, 5);
 x_64 = x_33;
} else {
 lean_dec_ref(x_33);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_34, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_34, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_67 = x_34;
} else {
 lean_dec_ref(x_34);
 x_67 = lean_box(0);
}
lean_inc(x_58);
x_68 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_66, x_2, x_58);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 6, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_62);
lean_ctor_set(x_70, 5, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_32);
if (x_72 == 0)
{
return x_32;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_32, 0);
x_74 = lean_ctor_get(x_32, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_32);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_31, 0);
lean_inc(x_76);
lean_dec(x_31);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_4);
return x_77;
}
}
case 7:
{
lean_object* x_78; 
x_78 = l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__7(x_1, x_2, x_3, x_4);
return x_78;
}
case 9:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Lean_Literal_type(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_4);
return x_81;
}
case 10:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
x_2 = x_82;
goto _start;
}
case 11:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_4, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__1(x_88, x_2);
lean_dec(x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = l___private_Init_Lean_Meta_30__inferProjType___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__9(x_1, x_84, x_85, x_86, x_3, x_4);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_91, 2);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_92);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_100 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_99, x_2, x_94);
lean_ctor_set(x_92, 1, x_100);
return x_90;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
lean_inc(x_94);
x_103 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_102, x_2, x_94);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_91, 2, x_104);
return x_90;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_91, 0);
x_106 = lean_ctor_get(x_91, 1);
x_107 = lean_ctor_get(x_91, 3);
x_108 = lean_ctor_get(x_91, 4);
x_109 = lean_ctor_get(x_91, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_91);
x_110 = lean_ctor_get(x_92, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_92, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_112 = x_92;
} else {
 lean_dec_ref(x_92);
 x_112 = lean_box(0);
}
lean_inc(x_94);
x_113 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_111, x_2, x_94);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_106);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_107);
lean_ctor_set(x_115, 4, x_108);
lean_ctor_set(x_115, 5, x_109);
lean_ctor_set(x_90, 1, x_115);
return x_90;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_ctor_get(x_90, 0);
lean_inc(x_116);
lean_dec(x_90);
x_117 = lean_ctor_get(x_91, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_91, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_91, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_91, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_91, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_122 = x_91;
} else {
 lean_dec_ref(x_91);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_92, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_92, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_125 = x_92;
} else {
 lean_dec_ref(x_92);
 x_125 = lean_box(0);
}
lean_inc(x_116);
x_126 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_36__checkInferTypeCache___spec__4(x_124, x_2, x_116);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
if (lean_is_scalar(x_122)) {
 x_128 = lean_alloc_ctor(0, 6, 0);
} else {
 x_128 = x_122;
}
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_118);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_119);
lean_ctor_set(x_128, 4, x_120);
lean_ctor_set(x_128, 5, x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_90);
if (x_130 == 0)
{
return x_90;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_90, 0);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_90);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_89, 0);
lean_inc(x_134);
lean_dec(x_89);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_4);
return x_135;
}
}
default: 
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_4);
return x_137;
}
}
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_37__inferTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_37__inferTypeAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_LOption(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_Class(lean_object*);
lean_object* initialize_Init_Lean_WHNF(lean_object*);
lean_object* initialize_Init_Lean_ReducibilityAttrs(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Class(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ReducibilityAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_TransparencyMode_Inhabited = _init_l_Lean_Meta_TransparencyMode_Inhabited();
l_Lean_Meta_TransparencyMode_HasBeq___closed__1 = _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq___closed__1);
l_Lean_Meta_TransparencyMode_HasBeq = _init_l_Lean_Meta_TransparencyMode_HasBeq();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq);
l_Lean_Meta_TransparencyMode_Hashable___closed__1 = _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable___closed__1);
l_Lean_Meta_TransparencyMode_Hashable = _init_l_Lean_Meta_TransparencyMode_Hashable();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable);
l_Lean_Meta_Exception_inhabited___closed__1 = _init_l_Lean_Meta_Exception_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_inhabited___closed__1);
l_Lean_Meta_Exception_inhabited = _init_l_Lean_Meta_Exception_inhabited();
lean_mark_persistent(l_Lean_Meta_Exception_inhabited);
l_Lean_Meta_tracer___closed__1 = _init_l_Lean_Meta_tracer___closed__1();
lean_mark_persistent(l_Lean_Meta_tracer___closed__1);
l_Lean_Meta_tracer___closed__2 = _init_l_Lean_Meta_tracer___closed__2();
lean_mark_persistent(l_Lean_Meta_tracer___closed__2);
l_Lean_Meta_tracer___closed__3 = _init_l_Lean_Meta_tracer___closed__3();
lean_mark_persistent(l_Lean_Meta_tracer___closed__3);
l_Lean_Meta_tracer___closed__4 = _init_l_Lean_Meta_tracer___closed__4();
lean_mark_persistent(l_Lean_Meta_tracer___closed__4);
l_Lean_Meta_tracer = _init_l_Lean_Meta_tracer();
lean_mark_persistent(l_Lean_Meta_tracer);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__1 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__1();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__1);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__2 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__2();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_21__cacheWHNF___spec__1___closed__2);
l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1 = _init_l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__1);
l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2 = _init_l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_Meta_22__whnfAux___main___spec__2___closed__2);
l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1 = _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1();
lean_mark_persistent(l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_22__whnfAux___main___spec__6___closed__1);
l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1 = _init_l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_forallTelescope___at___private_Init_Lean_Meta_32__inferForallType___spec__2___closed__1);
l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1 = _init_l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_Meta_37__inferTypeAux___main___spec__1___closed__1);
l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1 = _init_l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__1);
l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2 = _init_l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_37__inferTypeAux___main___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
