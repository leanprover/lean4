// Lean compiler output
// Module: Init.Lean.Meta.WHNF
// Imports: Init.Lean.AuxRecursor Init.Lean.WHNF Init.Lean.Meta.Basic
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
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_WHNF_5__toCtorWhenK___spec__1(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
size_t l_USize_shift__right(size_t, size_t);
extern lean_object* l_Lean_smartUnfoldingSuffix;
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_4__whnfAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_Hashable___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_3__toCtorIfLit(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_WHNF_6__isIdRhsApp(lean_object*);
lean_object* l___private_Init_Lean_WHNF_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_3__cacheWHNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_noConfusionExt;
lean_object* l___private_Init_Lean_WHNF_7__extractIdRhs(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__1;
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__2;
extern lean_object* l_unreachable_x21___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
extern lean_object* l_unreachable_x21___rarg___closed__2;
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_4__whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_inhabited;
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1;
lean_object* l_Lean_Meta_getExprMVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_object* l___private_Init_Lean_Meta_WHNF_2__getCachedWHNF(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_valueOpt(lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2;
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
extern lean_object* l_Lean_Expr_HasBeq;
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_auxRecExt;
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
extern lean_object* l_Lean_Expr_Hashable;
lean_object* l_Prod_HasBeq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_TransparencyMode_HasBeq;
extern lean_object* l_Lean_Meta_TransparencyMode_Hashable;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_3__cacheWHNF(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_26 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2(x_24, x_25, x_3);
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
x_31 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3(x_28, x_29, lean_box(0), x_30, x_3);
return x_31;
}
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2(x_3, x_9, x_2);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_2__getCachedWHNF(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__2(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_WHNF_2__getCachedWHNF(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_24 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_6, x_23, x_1, x_9, x_10);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_58 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_55, x_56, x_57, x_4, x_5);
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
x_63 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_60, x_61, x_62, x_4, x_5);
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
x_106 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_102, x_104, x_105, x_4, x_5);
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
x_114 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__3(x_1, x_113, x_4, x_5);
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
x_123 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4(x_3, x_120, x_121, x_120, x_113, x_122);
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
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__1() {
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
lean_object* _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__2() {
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
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_16 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_5, x_15, x_7, x_2, x_3);
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
x_28 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_17, x_27, x_19, x_2, x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_3__cacheWHNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_11, x_13, x_2);
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
x_21 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_17, x_20, x_2);
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
x_37 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_32, x_36, x_2);
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_3__cacheWHNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_WHNF_3__cacheWHNF(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1;
x_2 = l_Lean_Expr_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2;
x_21 = lean_panic_fn(x_19);
x_22 = lean_apply_2(x_21, x_5, x_6);
return x_22;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_23, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_21 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_20, x_10, x_11);
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
x_29 = l_Lean_Meta_getConst(x_28, x_10, x_26);
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
x_51 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_50, x_10, x_44);
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
lean_object* l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l___private_Init_Lean_WHNF_1__getFirstCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__8(x_1, x_7, x_4, x_5);
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
lean_object* _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getConst___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_9, x_6, x_10);
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
x_21 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_22 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_21, x_13, x_20, x_6, x_14);
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
x_91 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_92 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_91, x_13, x_89, x_6, x_14);
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
x_162 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_163 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_162, x_153, x_161, x_6, x_154);
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
x_206 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_207 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_206, x_153, x_204, x_6, x_154);
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
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_19, x_10, x_11);
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
x_103 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_102, x_10, x_22);
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
x_104 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6(x_1, x_2, x_3, x_7, x_21, x_10, x_22);
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
x_63 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_62, x_10, x_25);
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
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9(x_3, x_4, x_5, x_1, x_13, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9(x_3, x_4, x_5, x_1, x_12, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10(x_4, x_13, x_14, x_15, x_16, x_6, x_7);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1___boxed), 8, 5);
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
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment___boxed), 3, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__2), 8, 5);
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
x_31 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_30, x_6, x_7);
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
x_38 = l_Lean_Meta_getConst(x_36, x_6, x_34);
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
x_52 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_51, x_6, x_50);
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
x_72 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3(x_1, x_2, x_3, x_5, x_30, x_33, x_49, x_37, x_71, x_6, x_64);
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
x_82 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4(x_1, x_2, x_3, x_5, x_30, x_33, x_74, x_37, x_81, x_6, x_73);
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
x_92 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5(x_1, x_2, x_3, x_5, x_30, x_33, x_84, x_37, x_91, x_6, x_83);
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
x_113 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_112, x_6, x_34);
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
x_119 = l_Lean_Meta_getConst(x_117, x_6, x_115);
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
x_130 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_129, x_6, x_128);
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
x_147 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3(x_1, x_2, x_3, x_5, x_30, x_114, x_127, x_118, x_146, x_6, x_139);
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
x_157 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4(x_1, x_2, x_3, x_5, x_30, x_114, x_149, x_118, x_156, x_6, x_148);
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
x_167 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5(x_1, x_2, x_3, x_5, x_30, x_114, x_159, x_118, x_166, x_6, x_158);
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
x_187 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_186, x_6, x_115);
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
x_195 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_194, x_6, x_7);
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
x_200 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_199, x_6, x_7);
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
x_206 = l_Lean_Meta_getConst(x_205, x_6, x_203);
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
x_247 = l_Lean_Meta_getConst(x_246, x_6, x_244);
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
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1;
x_8 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9(x_1, x_2, x_3, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_16, x_7, x_8);
return x_17;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_23, x_10, x_11);
return x_24;
}
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_21 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_20, x_10, x_11);
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
x_29 = l_Lean_Meta_getConst(x_28, x_10, x_26);
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
x_51 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_50, x_10, x_44);
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
lean_object* l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_9, x_6, x_10);
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
x_21 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_22 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_21, x_13, x_20, x_6, x_14);
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
x_91 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_13);
x_92 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_91, x_13, x_89, x_6, x_14);
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
x_162 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_163 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_162, x_153, x_161, x_6, x_154);
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
x_206 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1;
lean_inc(x_6);
lean_inc(x_153);
x_207 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_206, x_153, x_204, x_6, x_154);
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
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_19, x_10, x_11);
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
x_103 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_102, x_10, x_22);
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
x_104 = l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__20(x_1, x_2, x_3, x_7, x_21, x_10, x_22);
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
x_63 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_62, x_10, x_25);
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
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21(x_3, x_4, x_5, x_1, x_13, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21(x_3, x_4, x_5, x_1, x_12, x_7, x_8);
return x_13;
}
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22(x_4, x_13, x_14, x_15, x_16, x_6, x_7);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1___boxed), 8, 5);
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
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_getExprMVarAssignment___boxed), 3, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__2), 8, 5);
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
x_31 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_30, x_6, x_7);
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
x_38 = l_Lean_Meta_getConst(x_36, x_6, x_34);
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
x_52 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_51, x_6, x_50);
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
x_72 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17(x_1, x_2, x_3, x_5, x_30, x_33, x_49, x_37, x_71, x_6, x_64);
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
x_82 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18(x_1, x_2, x_3, x_5, x_30, x_33, x_74, x_37, x_81, x_6, x_73);
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
x_92 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19(x_1, x_2, x_3, x_5, x_30, x_33, x_84, x_37, x_91, x_6, x_83);
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
x_113 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_112, x_6, x_34);
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
x_119 = l_Lean_Meta_getConst(x_117, x_6, x_115);
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
x_130 = l___private_Init_Lean_Meta_WHNF_1__isAuxDef_x3f(x_129, x_6, x_128);
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
x_147 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17(x_1, x_2, x_3, x_5, x_30, x_114, x_127, x_118, x_146, x_6, x_139);
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
x_157 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18(x_1, x_2, x_3, x_5, x_30, x_114, x_149, x_118, x_156, x_6, x_148);
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
x_167 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19(x_1, x_2, x_3, x_5, x_30, x_114, x_159, x_118, x_166, x_6, x_158);
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
x_187 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_186, x_6, x_115);
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
x_195 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_194, x_6, x_7);
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
x_200 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_199, x_6, x_7);
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
x_206 = l_Lean_Meta_getConst(x_205, x_6, x_203);
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
x_247 = l_Lean_Meta_getConst(x_246, x_6, x_244);
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
lean_object* l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1;
x_8 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21(x_1, x_2, x_3, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__23(x_1, x_2, x_3, x_16, x_7, x_17);
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
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_15, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__23(x_1, x_2, x_3, x_17, x_7, x_18);
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
lean_object* l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_15 = l_Lean_Meta_getConst(x_13, x_5, x_6);
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
x_33 = l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24(x_1, x_2, x_3, x_25, x_14, x_32, x_5, x_24);
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
x_43 = l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25(x_1, x_2, x_3, x_35, x_14, x_42, x_5, x_34);
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
x_59 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_58, x_5, x_6);
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
lean_object* l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__16(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l_Lean_getStuckMVar___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__23(x_1, x_2, x_3, x_8, x_5, x_9);
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
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l___private_Init_Lean_WHNF_10__whnfCoreUnstuck___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__15(x_1, x_2, x_3, x_18, x_8, x_9);
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
x_25 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_24, x_8, x_22);
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
x_31 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_30, x_8, x_27);
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
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_18, x_8, x_9);
return x_19;
}
}
}
lean_object* l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_Lean_Meta_getConst(x_8, x_6, x_7);
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
x_18 = l___private_Init_Lean_WHNF_8__deltaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__12(x_1, x_2, x_3, x_4, x_16, x_9, x_6, x_17);
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
x_31 = l_Lean_Meta_getConst(x_29, x_6, x_7);
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
x_49 = l_Lean_Meta_getConst(x_48, x_6, x_38);
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
x_55 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__13(x_1, x_2, x_3, x_4, x_40, x_30, x_54, x_6, x_51);
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
x_61 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__14(x_1, x_2, x_3, x_4, x_40, x_30, x_60, x_6, x_57);
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
x_66 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__26(x_1, x_2, x_3, x_4, x_56, x_30, x_65, x_6, x_62);
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
x_71 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__27(x_1, x_2, x_3, x_4, x_40, x_30, x_70, x_6, x_67);
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
x_76 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__28(x_1, x_2, x_3, x_4, x_40, x_30, x_75, x_6, x_72);
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
x_81 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__29(x_1, x_2, x_3, x_4, x_40, x_30, x_80, x_6, x_77);
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
x_86 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__30(x_1, x_2, x_3, x_4, x_40, x_30, x_85, x_6, x_82);
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
x_91 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__31(x_1, x_2, x_3, x_4, x_40, x_30, x_90, x_6, x_87);
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
x_96 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__32(x_1, x_2, x_3, x_4, x_40, x_30, x_95, x_6, x_92);
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
x_112 = l_Lean_Meta_getConst(x_111, x_6, x_101);
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
x_118 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__13(x_1, x_2, x_3, x_4, x_102, x_30, x_117, x_6, x_114);
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
x_124 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__14(x_1, x_2, x_3, x_4, x_102, x_30, x_123, x_6, x_120);
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
x_129 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__26(x_1, x_2, x_3, x_4, x_119, x_30, x_128, x_6, x_125);
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
x_134 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__27(x_1, x_2, x_3, x_4, x_102, x_30, x_133, x_6, x_130);
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
x_139 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__28(x_1, x_2, x_3, x_4, x_102, x_30, x_138, x_6, x_135);
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
x_144 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__29(x_1, x_2, x_3, x_4, x_102, x_30, x_143, x_6, x_140);
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
x_149 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__30(x_1, x_2, x_3, x_4, x_102, x_30, x_148, x_6, x_145);
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
x_154 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__31(x_1, x_2, x_3, x_4, x_102, x_30, x_153, x_6, x_150);
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
x_159 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__32(x_1, x_2, x_3, x_4, x_102, x_30, x_158, x_6, x_155);
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
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_inc(x_5);
x_13 = l_Lean_Meta_getLocalDecl(x_12, x_5, x_6);
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
x_42 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_39, x_41);
lean_dec(x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc_n(x_44, 2);
x_46 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(x_1, x_2, x_3, x_44, x_44, x_5, x_45);
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
x_58 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_55, x_57, x_50);
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
x_63 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_59, x_62, x_50);
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
x_75 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_70, x_74, x_50);
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
x_90 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_85, x_89, x_78);
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
x_110 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_107, x_109);
lean_dec(x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc_n(x_112, 2);
x_114 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(x_1, x_2, x_3, x_112, x_112, x_5, x_113);
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
x_126 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_123, x_125, x_118);
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
x_131 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_127, x_130, x_118);
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
x_143 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_138, x_142, x_118);
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
x_158 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_153, x_157, x_146);
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
x_178 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_175, x_177);
lean_dec(x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_179 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc_n(x_180, 2);
x_182 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(x_1, x_2, x_3, x_180, x_180, x_5, x_181);
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
x_194 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_191, x_193, x_186);
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
x_199 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_195, x_198, x_186);
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
x_211 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_206, x_210, x_186);
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
x_226 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_221, x_225, x_214);
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
x_248 = l_PersistentHashMap_find___at___private_Init_Lean_Meta_WHNF_2__getCachedWHNF___spec__1(x_245, x_247);
lean_dec(x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_249 = l_Lean_whnfCore___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc_n(x_250, 2);
x_252 = l_Lean_unfoldDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__11(x_1, x_2, x_3, x_250, x_250, x_5, x_251);
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
x_264 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_261, x_263, x_256);
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
x_269 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_265, x_268, x_256);
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
x_281 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_276, x_280, x_256);
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
x_296 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1(x_291, x_295, x_284);
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
lean_object* l___private_Init_Lean_Meta_WHNF_4__whnfAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_WHNF_2__mkNullaryCtor___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_WHNF_9__deltaBetaDefinition___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceQuotRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_reduceRec___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__21___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isQuotRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isRecStuck___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_WHNF_4__whnfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_whnfEasyCases___main___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_WHNF(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__1 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__1();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__1);
l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__2 = _init_l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__2();
lean_mark_persistent(l_PersistentHashMap_insert___at___private_Init_Lean_Meta_WHNF_3__cacheWHNF___spec__1___closed__2);
l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1 = _init_l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__1);
l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2 = _init_l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2();
lean_mark_persistent(l_panicWithPos___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__2___closed__2);
l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1 = _init_l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1();
lean_mark_persistent(l___private_Init_Lean_WHNF_5__toCtorWhenK___at___private_Init_Lean_Meta_WHNF_4__whnfAux___main___spec__6___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
