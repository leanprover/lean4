// Lean compiler output
// Module: Init.Lean.WHNFUtil
// Imports: Init.Lean.Environment Init.Lean.AuxRecursor Init.Lean.ProjFns
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
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_WHNFUtil_9__isIdRhsApp(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___boxed(lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases(lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13(lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_10__extractIdRhs(lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___boxed(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2;
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5;
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2;
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4;
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_reduceProjectionFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFn___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___boxed(lean_object*);
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___boxed(lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main(lean_object*);
extern lean_object* l_unreachable_x21___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7;
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8;
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1(lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_reduceRecAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___boxed(lean_object*);
lean_object* l_Lean_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
extern lean_object* l_unreachable_x21___rarg___closed__2;
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_1__getFirstCtor(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck(lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7(lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___boxed(lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___boxed(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___boxed(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main(lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_valueOpt(lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_reduceRec(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6;
lean_object* l_Lean_reduceProjectionFnAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1;
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2___boxed(lean_object**);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___boxed(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1(lean_object*);
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___boxed(lean_object*);
uint8_t l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1;
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_auxRecExt;
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1___boxed(lean_object**);
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___boxed(lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___boxed(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___boxed(lean_object*);
lean_object* l_Lean_reduceQuotRecAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5(lean_object*);
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12(lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* lean_expr_mk_lit(lean_object*);
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceProjectionFn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_WHNFUtil_1__getFirstCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; 
lean_free_object(x_3);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_12);
x_18 = lean_box(0);
return x_18;
}
}
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___private_Init_Lean_WHNFUtil_1__getFirstCtor(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_expr_mk_const(x_10, x_6);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_12);
x_14 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_15, x_17);
x_19 = l_Array_shrink___main___rarg(x_18, x_3);
x_20 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_19, x_19, x_12, x_11);
lean_dec(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_expr_mk_const(x_21, x_6);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_23);
x_25 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
x_29 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_26, x_28);
x_30 = l_Array_shrink___main___rarg(x_29, x_3);
x_31 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_30, x_30, x_23, x_22);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2;
x_2 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2;
x_2 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_3__toCtorIfLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_expr_mk_lit(x_2);
x_10 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5;
x_11 = lean_expr_mk_app(x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_free_object(x_2);
lean_dec(x_4);
x_12 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8;
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_expr_mk_lit(x_18);
x_20 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5;
x_21 = lean_expr_mk_app(x_20, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_13);
x_22 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8;
return x_22;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
return x_1;
}
}
}
uint8_t l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_dec_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_find___main___rarg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_4__getRecRuleFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_WHNFUtil_4__getRecRuleFor(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_expr_has_expr_mvar(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_2(x_1, x_2, x_6);
x_8 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_getAppFn___main(x_7);
x_9 = l_Lean_RecursorVal_getInduct(x_1);
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_15; 
x_15 = lean_expr_has_expr_mvar(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_7);
x_17 = l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor(x_3, x_7, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_21);
x_22 = lean_apply_1(x_4, x_21);
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__2), 6, 5);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_7);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_6);
x_24 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_25);
x_27 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
lean_inc(x_7);
x_31 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_7, x_28, x_30);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_32);
x_33 = l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_7);
x_34 = l___private_Init_Lean_WHNFUtil_2__mkNullaryCtor(x_3, x_7, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_36, lean_box(0), x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_38);
x_39 = lean_apply_1(x_4, x_38);
lean_inc(x_6);
x_40 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__2), 6, 5);
lean_closure_set(x_40, 0, x_5);
lean_closure_set(x_40, 1, x_7);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_38);
lean_closure_set(x_40, 4, x_6);
x_41 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_39, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
return x_45;
}
}
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_1(x_1, x_8);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__3), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_7);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_3);
x_9 = lean_apply_1(x_3, x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__4), 8, 7);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_3);
lean_closure_set(x_10, 5, x_4);
lean_closure_set(x_10, 6, x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMAux___main___at___private_Init_Lean_WHNFUtil_5__toCtorWhenK___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_5__toCtorWhenK(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit(x_8);
lean_inc(x_1);
x_10 = l___private_Init_Lean_WHNFUtil_4__getRecRuleFor(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_14);
x_16 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_9, x_17, x_19);
x_21 = l_List_lengthAux___main___rarg(x_3, x_14);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_lengthAux___main___rarg(x_23, x_14);
x_25 = lean_nat_dec_eq(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_apply_1(x_2, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_13, 2);
lean_inc(x_28);
x_29 = lean_instantiate_lparams(x_28, x_23, x_3);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 4);
lean_inc(x_31);
x_32 = lean_nat_add(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
x_35 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_34, x_4, x_14, x_29);
lean_dec(x_34);
x_36 = lean_array_get_size(x_20);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_nat_sub(x_36, x_37);
lean_dec(x_37);
x_39 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_36, x_20, x_38, x_35);
lean_dec(x_20);
lean_dec(x_36);
x_40 = lean_nat_add(x_5, x_18);
x_41 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_6, x_4, x_40, x_39);
x_42 = lean_apply_1(x_7, x_41);
return x_42;
}
}
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_14);
x_20 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_19, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_14);
lean_inc(x_8);
x_21 = l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg(x_8, x_10, x_11, x_12, x_13, x_1, x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__2), 3, 2);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_14);
lean_inc(x_9);
x_23 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_21, x_22);
x_24 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_23, x_16);
return x_24;
}
}
}
lean_object* l_Lean_reduceRecAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_RecursorVal_getMajorIdx(x_6);
x_12 = lean_array_get_size(x_8);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_8, x_11);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_2);
x_18 = lean_apply_1(x_2, x_16);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__3), 14, 13);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_7);
lean_closure_set(x_19, 3, x_8);
lean_closure_set(x_19, 4, x_11);
lean_closure_set(x_19, 5, x_12);
lean_closure_set(x_19, 6, x_10);
lean_closure_set(x_19, 7, x_1);
lean_closure_set(x_19, 8, x_17);
lean_closure_set(x_19, 9, x_2);
lean_closure_set(x_19, 10, x_3);
lean_closure_set(x_19, 11, x_4);
lean_closure_set(x_19, 12, x_5);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Lean_reduceRecAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg), 10, 0);
return x_3;
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceRecAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_reduceRecAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceRecAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_environment_find(x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_13);
x_15 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_16, x_18);
x_20 = lean_apply_3(x_4, x_12, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_3, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_3, x_23);
return x_24;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_6__matchRecApp___rarg), 4, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_6__matchRecApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_WHNFUtil_6__matchRecApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_reduceRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = lean_environment_find(x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_17);
x_19 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_6, x_20, x_22);
x_24 = l_Lean_reduceRecAux___rarg(x_1, x_2, x_3, x_4, x_5, x_16, x_11, x_23, x_7, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_7, x_25);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_7, x_27);
return x_28;
}
}
}
lean_object* l_Lean_reduceRec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceRec___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_reduceRec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceRec(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_isRecStuck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_environment_find(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_16);
x_18 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_19, x_21);
x_23 = l_Lean_RecursorVal_getMajorIdx(x_14);
lean_dec(x_14);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_1(x_2, x_30);
x_33 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_32, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_apply_2(x_35, lean_box(0), x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = lean_apply_2(x_39, lean_box(0), x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
return x_45;
}
}
}
lean_object* l_Lean_isRecStuck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isRecStuck___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_isRecStuck___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isRecStuck(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_environment_find(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_20 = lean_box(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_21 = l_Lean_exprIsInhabited;
x_22 = lean_array_get(x_21, x_3, x_4);
x_23 = lean_expr_mk_app(x_22, x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
x_26 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_6, x_3, x_25, x_23);
x_27 = lean_apply_1(x_7, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_30 = lean_box(0);
x_31 = lean_apply_1(x_1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_apply_1(x_1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_apply_1(x_1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_apply_1(x_1, x_38);
return x_39;
}
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_21; lean_object* x_22; 
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_22 = lean_box(x_21);
switch (lean_obj_tag(x_22)) {
case 2:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_unsigned_to_nat(3u);
x_9 = x_23;
x_10 = x_24;
goto block_20;
}
case 3:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(4u);
x_26 = lean_unsigned_to_nat(3u);
x_9 = x_25;
x_10 = x_26;
goto block_20;
}
default: 
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_7, x_27);
return x_28;
}
}
block_20:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_6, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_2, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_18, 0, x_7);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_9);
lean_closure_set(x_18, 5, x_11);
lean_closure_set(x_18, 6, x_8);
x_19 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_reduceQuotRecAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceQuotRecAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceQuotRecAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_reduceQuotRecAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceQuotRecAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_environment_find(x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_13);
x_15 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_16, x_18);
x_20 = lean_apply_3(x_4, x_12, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_3, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_3, x_23);
return x_24;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp___rarg), 4, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_WHNFUtil_7__matchQuotRecApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_reduceQuotRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn___main(x_4);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = lean_environment_find(x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_5, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_15);
x_17 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_18, x_20);
x_22 = l_Lean_reduceQuotRecAux___rarg(x_1, x_2, x_3, x_14, x_9, x_21, x_5, x_6);
lean_dec(x_9);
lean_dec(x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_5, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_5, x_25);
return x_26;
}
}
}
lean_object* l_Lean_reduceQuotRec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceQuotRec___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_reduceQuotRec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceQuotRec(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_isQuotRecStuck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_environment_find(x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_6 = x_15;
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_18);
x_20 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_21, x_23);
x_25 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
x_26 = lean_box(x_25);
switch (lean_obj_tag(x_26)) {
case 2:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_nat_dec_lt(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_6 = x_30;
goto block_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_array_fget(x_24, x_28);
lean_dec(x_24);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_apply_1(x_2, x_31);
x_34 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_3);
return x_34;
}
}
case 3:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_array_get_size(x_24);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_dec_lt(x_36, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_6 = x_38;
goto block_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_fget(x_24, x_36);
lean_dec(x_24);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_apply_1(x_2, x_39);
x_42 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_41, x_3);
return x_42;
}
}
default: 
{
lean_object* x_43; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
x_6 = x_43;
goto block_11;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_6 = x_44;
goto block_11;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(0);
x_6 = x_45;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_isQuotRecStuck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isQuotRecStuck___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_isQuotRecStuck___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isQuotRecStuck(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceProjectionFnAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_8);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_environment_find(x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_nat_add(x_4, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_16);
x_18 = lean_nat_dec_lt(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_21 = lean_nat_sub(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = l_Lean_Expr_getRevArg_x21___main(x_8, x_23);
x_25 = lean_nat_add(x_4, x_22);
x_26 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_5, x_6, x_25, x_24);
x_27 = lean_apply_1(x_7, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_1, x_28);
return x_29;
}
}
}
lean_object* l_Lean_reduceProjectionFnAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_5, x_8);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_2, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_reduceProjectionFnAux___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_8);
lean_closure_set(x_16, 4, x_9);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_7);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
lean_object* l_Lean_reduceProjectionFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceProjectionFnAux___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_reduceProjectionFnAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceProjectionFnAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_reduceProjectionFnAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceProjectionFnAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_reduceProjectionFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn___main(x_4);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_3);
x_9 = lean_environment_find(x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_ConstantInfo_name(x_12);
lean_dec(x_12);
lean_inc(x_3);
x_14 = lean_get_projection_info(x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_18);
x_20 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_21, x_23);
x_25 = l_Lean_reduceProjectionFnAux___rarg(x_1, x_2, x_3, x_17, x_24, x_5, x_6);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_apply_1(x_5, x_26);
return x_27;
}
}
}
lean_object* l_Lean_reduceProjectionFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceProjectionFn___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_reduceProjectionFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceProjectionFn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalDecl_valueOpt(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg(x_3, x_4, x_5, x_12, x_6);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg(x_3, x_4, x_5, x_11, x_6);
return x_12;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_unreachable_x21___rarg___closed__1;
x_12 = lean_unsigned_to_nat(37u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_unreachable_x21___rarg___closed__2;
x_15 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg(x_1, x_11, x_12, x_13, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_2);
x_18 = lean_apply_1(x_2, x_16);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_5);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_3);
x_23 = lean_apply_1(x_3, x_21);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_2);
lean_closure_set(x_24, 4, x_3);
lean_closure_set(x_24, 5, x_5);
x_25 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
case 4:
{
lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_apply_1(x_5, x_4);
return x_26;
}
case 5:
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_apply_1(x_5, x_4);
return x_27;
}
case 8:
{
lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_apply_1(x_5, x_4);
return x_28;
}
case 10:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_4 = x_29;
goto _start;
}
case 11:
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_apply_1(x_5, x_4);
return x_31;
}
default: 
{
lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_6 = x_32;
goto block_10;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idRhs");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_WHNFUtil_9__isIdRhsApp(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_WHNFUtil_9__isIdRhsApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_10__extractIdRhs(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_9__isIdRhsApp(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_3);
x_5 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_4);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_1);
x_9 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_1, x_6, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = l_Lean_exprIsInhabited;
x_14 = lean_array_get(x_13, x_9, x_7);
x_15 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_10, x_9, x_11, x_14);
lean_dec(x_9);
lean_dec(x_10);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_1;
}
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_ConstantInfo_lparams(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthAux___main___rarg(x_6, x_7);
lean_dec(x_6);
x_9 = l_List_lengthAux___main___rarg(x_2, x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_13 = lean_instantiate_value_lparams(x_1, x_2);
x_14 = l_Lean_Expr_betaRev(x_13, x_3);
lean_dec(x_13);
x_15 = l___private_Init_Lean_WHNFUtil_10__extractIdRhs(x_14);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___rarg), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_24; 
x_24 = l_Lean_Expr_getAppFn___main(x_18);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_environment_find(x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_27 = lean_expr_eqv(x_1, x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_31 = lean_apply_2(x_29, lean_box(0), x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_19 = x_32;
goto block_23;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_6, 2);
x_34 = lean_nat_add(x_7, x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_35);
x_37 = lean_nat_dec_lt(x_34, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_38 = lean_expr_eqv(x_1, x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_42 = lean_apply_2(x_40, lean_box(0), x_41);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_box(0);
x_19 = x_43;
goto block_23;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_44 = lean_nat_sub(x_36, x_34);
lean_dec(x_34);
lean_dec(x_36);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_44, x_45);
lean_dec(x_44);
x_47 = l_Lean_Expr_getRevArg_x21___main(x_18, x_46);
x_48 = lean_nat_add(x_7, x_45);
x_49 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_8, x_9, x_48, x_47);
x_50 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_51 = lean_expr_eqv(x_1, x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_55 = lean_apply_2(x_53, lean_box(0), x_54);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
x_19 = x_56;
goto block_23;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_4);
return x_22;
}
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_expr_eqv(x_11, x_12);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_updateFn___main(x_10, x_12);
lean_dec(x_12);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_2(x_25, lean_box(0), x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_array_fget(x_15, x_16);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_2);
x_29 = lean_apply_1(x_2, x_27);
x_30 = lean_box(x_8);
x_31 = lean_box(x_9);
x_32 = lean_alloc_closure((void*)(l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1___boxed), 18, 17);
lean_closure_set(x_32, 0, x_11);
lean_closure_set(x_32, 1, x_12);
lean_closure_set(x_32, 2, x_1);
lean_closure_set(x_32, 3, x_10);
lean_closure_set(x_32, 4, x_13);
lean_closure_set(x_32, 5, x_14);
lean_closure_set(x_32, 6, x_16);
lean_closure_set(x_32, 7, x_17);
lean_closure_set(x_32, 8, x_15);
lean_closure_set(x_32, 9, x_2);
lean_closure_set(x_32, 10, x_3);
lean_closure_set(x_32, 11, x_4);
lean_closure_set(x_32, 12, x_5);
lean_closure_set(x_32, 13, x_6);
lean_closure_set(x_32, 14, x_7);
lean_closure_set(x_32, 15, x_30);
lean_closure_set(x_32, 16, x_31);
x_33 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_29, x_32);
return x_33;
}
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___boxed), 15, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_ConstantInfo_lparams(x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_lengthAux___main___rarg(x_16, x_17);
lean_dec(x_16);
x_19 = l_List_lengthAux___main___rarg(x_14, x_17);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_expr_eqv(x_11, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Expr_updateFn___main(x_10, x_12);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_apply_2(x_27, lean_box(0), x_10);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
x_29 = lean_instantiate_value_lparams(x_13, x_14);
x_30 = l_Lean_Expr_betaRev(x_29, x_15);
lean_dec(x_29);
x_31 = l___private_Init_Lean_WHNFUtil_10__extractIdRhs(x_30);
x_32 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
return x_32;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg___boxed), 15, 0);
return x_2;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
if (lean_obj_tag(x_18) == 5)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 5)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_environment_find(x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_30 = lean_expr_eqv(x_1, x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_19 = x_35;
goto block_23;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
x_39 = lean_box(x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_4);
x_40 = l_Lean_exprIsInhabited;
x_41 = lean_array_get(x_40, x_6, x_7);
x_42 = lean_expr_mk_app(x_41, x_27);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_8, x_43);
x_45 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_9, x_6, x_44, x_42);
x_46 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_47 = lean_expr_eqv(x_1, x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec(x_3);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_51 = lean_apply_2(x_49, lean_box(0), x_50);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_19 = x_52;
goto block_23;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_53 = lean_expr_eqv(x_1, x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
lean_dec(x_3);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_57 = lean_apply_2(x_55, lean_box(0), x_56);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_19 = x_58;
goto block_23;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_59 = lean_expr_eqv(x_1, x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_3, 0);
lean_inc(x_60);
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_63 = lean_apply_2(x_61, lean_box(0), x_62);
return x_63;
}
else
{
lean_object* x_64; 
x_64 = lean_box(0);
x_19 = x_64;
goto block_23;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_65 = lean_expr_eqv(x_1, x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_69 = lean_apply_2(x_67, lean_box(0), x_68);
return x_69;
}
else
{
lean_object* x_70; 
x_70 = lean_box(0);
x_19 = x_70;
goto block_23;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_71 = lean_expr_eqv(x_1, x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_75 = lean_apply_2(x_73, lean_box(0), x_74);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_box(0);
x_19 = x_76;
goto block_23;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_77 = lean_expr_eqv(x_1, x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_3, 0);
lean_inc(x_78);
lean_dec(x_3);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Expr_updateFn___main(x_4, x_2);
x_81 = lean_apply_2(x_79, lean_box(0), x_80);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_box(0);
x_19 = x_82;
goto block_23;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_4);
return x_22;
}
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_22; lean_object* x_23; uint8_t x_40; lean_object* x_41; 
x_40 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_41 = lean_box(x_40);
switch (lean_obj_tag(x_41)) {
case 2:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_unsigned_to_nat(5u);
x_43 = lean_unsigned_to_nat(3u);
x_22 = x_42;
x_23 = x_43;
goto block_39;
}
case 3:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_unsigned_to_nat(3u);
x_22 = x_44;
x_23 = x_45;
goto block_39;
}
default: 
{
uint8_t x_46; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_expr_eqv(x_11, x_12);
lean_dec(x_11);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Expr_updateFn___main(x_10, x_12);
lean_dec(x_12);
x_50 = lean_apply_2(x_48, lean_box(0), x_49);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_12);
x_51 = lean_box(0);
x_17 = x_51;
goto block_21;
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_10);
return x_20;
}
block_39:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_16);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_expr_eqv(x_11, x_12);
lean_dec(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Expr_updateFn___main(x_10, x_12);
lean_dec(x_12);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_12);
x_31 = lean_box(0);
x_17 = x_31;
goto block_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_array_fget(x_16, x_22);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_2);
x_34 = lean_apply_1(x_2, x_32);
x_35 = lean_box(x_8);
x_36 = lean_box(x_9);
x_37 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1___boxed), 18, 17);
lean_closure_set(x_37, 0, x_11);
lean_closure_set(x_37, 1, x_12);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_10);
lean_closure_set(x_37, 4, x_13);
lean_closure_set(x_37, 5, x_16);
lean_closure_set(x_37, 6, x_23);
lean_closure_set(x_37, 7, x_22);
lean_closure_set(x_37, 8, x_24);
lean_closure_set(x_37, 9, x_2);
lean_closure_set(x_37, 10, x_3);
lean_closure_set(x_37, 11, x_4);
lean_closure_set(x_37, 12, x_5);
lean_closure_set(x_37, 13, x_6);
lean_closure_set(x_37, 14, x_7);
lean_closure_set(x_37, 15, x_35);
lean_closure_set(x_37, 16, x_36);
x_38 = lean_apply_4(x_33, lean_box(0), lean_box(0), x_34, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Init_Lean_WHNFUtil_3__toCtorIfLit(x_18);
lean_inc(x_1);
x_25 = l___private_Init_Lean_WHNFUtil_4__getRecRuleFor(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_expr_eqv(x_2, x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Expr_updateFn___main(x_5, x_3);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_box(0);
x_19 = x_31;
goto block_23;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_24, x_33);
x_35 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_24, x_36, x_38);
x_40 = l_List_lengthAux___main___rarg(x_6, x_33);
x_41 = lean_ctor_get(x_1, 0);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_45 = lean_expr_eqv(x_2, x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Expr_updateFn___main(x_5, x_3);
x_49 = lean_apply_2(x_47, lean_box(0), x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_19 = x_50;
goto block_23;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
x_51 = lean_ctor_get(x_32, 2);
lean_inc(x_51);
x_52 = lean_instantiate_lparams(x_51, x_42, x_6);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = lean_ctor_get(x_1, 5);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_nat_add(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
x_58 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_57, x_7, x_33, x_52);
lean_dec(x_57);
x_59 = lean_array_get_size(x_39);
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_dec(x_32);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_60);
x_62 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_59, x_39, x_61, x_58);
lean_dec(x_39);
lean_dec(x_59);
x_63 = lean_nat_add(x_8, x_37);
x_64 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_9, x_7, x_63, x_62);
x_65 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_64);
return x_65;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_5);
return x_22;
}
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_22 = lean_box(x_16);
x_23 = lean_box(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1___boxed), 18, 17);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_7);
lean_closure_set(x_24, 7, x_8);
lean_closure_set(x_24, 8, x_9);
lean_closure_set(x_24, 9, x_10);
lean_closure_set(x_24, 10, x_11);
lean_closure_set(x_24, 11, x_12);
lean_closure_set(x_24, 12, x_13);
lean_closure_set(x_24, 13, x_14);
lean_closure_set(x_24, 14, x_15);
lean_closure_set(x_24, 15, x_22);
lean_closure_set(x_24, 16, x_23);
if (x_21 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_2(x_26, lean_box(0), x_20);
x_28 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_27, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_20);
lean_inc(x_4);
x_29 = l___private_Init_Lean_WHNFUtil_5__toCtorWhenK___rarg(x_4, x_10, x_11, x_12, x_19, x_1, x_20);
x_30 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__2), 3, 2);
lean_closure_set(x_30, 0, x_4);
lean_closure_set(x_30, 1, x_20);
lean_inc(x_18);
x_31 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_29, x_30);
x_32 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_31, x_24);
return x_32;
}
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_RecursorVal_getMajorIdx(x_14);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_expr_eqv(x_11, x_12);
lean_dec(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_updateFn___main(x_10, x_12);
lean_dec(x_12);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_2(x_26, lean_box(0), x_10);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_array_fget(x_16, x_17);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_2);
x_30 = lean_apply_1(x_2, x_28);
x_31 = lean_box(x_8);
x_32 = lean_box(x_9);
lean_inc(x_29);
x_33 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2___boxed), 20, 19);
lean_closure_set(x_33, 0, x_14);
lean_closure_set(x_33, 1, x_11);
lean_closure_set(x_33, 2, x_12);
lean_closure_set(x_33, 3, x_1);
lean_closure_set(x_33, 4, x_10);
lean_closure_set(x_33, 5, x_15);
lean_closure_set(x_33, 6, x_16);
lean_closure_set(x_33, 7, x_17);
lean_closure_set(x_33, 8, x_18);
lean_closure_set(x_33, 9, x_2);
lean_closure_set(x_33, 10, x_3);
lean_closure_set(x_33, 11, x_4);
lean_closure_set(x_33, 12, x_5);
lean_closure_set(x_33, 13, x_6);
lean_closure_set(x_33, 14, x_7);
lean_closure_set(x_33, 15, x_31);
lean_closure_set(x_33, 16, x_32);
lean_closure_set(x_33, 17, x_29);
lean_closure_set(x_33, 18, x_13);
x_34 = lean_apply_4(x_29, lean_box(0), lean_box(0), x_30, x_33);
return x_34;
}
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___boxed), 16, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_exprIsInhabited;
x_7 = l_monadInhabited___rarg(x_1, x_6);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_2);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_LocalDecl_valueOpt(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_17;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_18; 
x_18 = l_Lean_Expr_isLambda(x_12);
if (x_18 == 0)
{
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_4);
x_21 = lean_environment_find(x_4, x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_expr_eqv(x_1, x_12);
lean_dec(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Expr_updateFn___main(x_3, x_12);
lean_dec(x_12);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_12);
x_27 = lean_box(0);
x_13 = x_27;
goto block_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
switch (lean_obj_tag(x_28)) {
case 1:
{
if (x_11 == 0)
{
lean_object* x_54; 
lean_dec(x_20);
x_54 = lean_box(0);
x_29 = x_54;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_ConstantInfo_name(x_28);
x_56 = l_Lean_auxRecExt;
x_57 = l_Lean_TagDeclarationExtension_isTagged(x_56, x_4, x_55);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_20);
x_58 = lean_box(0);
x_29 = x_58;
goto block_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_59);
x_61 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_60);
x_62 = lean_mk_array(x_60, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_60, x_63);
lean_dec(x_60);
lean_inc(x_3);
x_65 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_3, x_62, x_64);
x_66 = l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg(x_2, x_6, x_7, x_8, x_9, x_10, x_4, x_11, x_5, x_3, x_1, x_12, x_28, x_20, x_65);
lean_dec(x_12);
lean_dec(x_1);
return x_66;
}
}
}
case 4:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_28, 0);
lean_inc(x_67);
lean_dec(x_28);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_68);
x_70 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_69);
x_71 = lean_mk_array(x_69, x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_69, x_72);
lean_dec(x_69);
lean_inc(x_3);
x_74 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_3, x_71, x_73);
lean_inc(x_4);
x_75 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg(x_2, x_6, x_7, x_8, x_9, x_10, x_4, x_11, x_5, x_3, x_1, x_12, x_4, x_67, x_20, x_74);
lean_dec(x_20);
lean_dec(x_67);
return x_75;
}
case 7:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_28, 0);
lean_inc(x_76);
lean_dec(x_28);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_77);
x_79 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_78);
x_80 = lean_mk_array(x_78, x_79);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_sub(x_78, x_81);
lean_dec(x_78);
lean_inc(x_3);
x_83 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_3, x_80, x_82);
lean_inc(x_4);
x_84 = l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg(x_2, x_6, x_7, x_8, x_9, x_10, x_4, x_11, x_5, x_3, x_1, x_12, x_4, x_76, x_20, x_83);
return x_84;
}
default: 
{
uint8_t x_85; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_85 = lean_expr_eqv(x_1, x_12);
lean_dec(x_1);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
lean_dec(x_2);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Expr_updateFn___main(x_3, x_12);
lean_dec(x_12);
x_89 = lean_apply_2(x_87, lean_box(0), x_88);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_12);
x_90 = lean_box(0);
x_13 = x_90;
goto block_17;
}
}
}
block_53:
{
lean_dec(x_29);
if (x_5 == 0)
{
uint8_t x_30; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_30 = lean_expr_eqv(x_1, x_12);
lean_dec(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Expr_updateFn___main(x_3, x_12);
lean_dec(x_12);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_12);
x_35 = lean_box(0);
x_13 = x_35;
goto block_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_ConstantInfo_name(x_28);
lean_dec(x_28);
lean_inc(x_4);
x_37 = lean_get_projection_info(x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = lean_expr_eqv(x_1, x_12);
lean_dec(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Expr_updateFn___main(x_3, x_12);
lean_dec(x_12);
x_42 = lean_apply_2(x_40, lean_box(0), x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_12);
x_43 = lean_box(0);
x_13 = x_43;
goto block_17;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_45);
x_47 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_46);
x_48 = lean_mk_array(x_46, x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_46, x_49);
lean_dec(x_46);
lean_inc(x_3);
x_51 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_3, x_48, x_50);
lean_inc(x_4);
x_52 = l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg(x_2, x_6, x_7, x_8, x_9, x_10, x_4, x_11, x_5, x_3, x_1, x_12, x_4, x_44, x_51);
return x_52;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_91 = lean_expr_eqv(x_1, x_12);
lean_dec(x_1);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Expr_updateFn___main(x_3, x_12);
lean_dec(x_12);
x_95 = lean_apply_2(x_93, lean_box(0), x_94);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_12);
x_96 = lean_box(0);
x_13 = x_96;
goto block_17;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_12);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_97);
x_99 = lean_mk_empty_array_with_capacity(x_98);
lean_dec(x_98);
x_100 = l___private_Init_Lean_Expr_3__getAppRevArgsAux___main(x_3, x_99);
x_101 = l_Lean_Expr_betaRev(x_1, x_100);
lean_dec(x_1);
x_102 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_2, x_6, x_7, x_8, x_9, x_10, x_4, x_11, x_5, x_101);
return x_102;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_3);
return x_16;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn___main(x_7);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_environment_find(x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_8 = x_16;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 6)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 3);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_nat_add(x_21, x_5);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_23);
x_25 = lean_nat_sub(x_24, x_22);
lean_dec(x_22);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_25);
x_28 = l_Lean_Expr_getRevArgD___main(x_7, x_27, x_6);
lean_dec(x_6);
x_29 = lean_apply_2(x_20, lean_box(0), x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_17);
x_30 = lean_box(0);
x_8 = x_30;
goto block_12;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_3);
x_31 = lean_box(0);
x_8 = x_31;
goto block_12;
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
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_unreachable_x21___rarg___closed__1;
x_17 = lean_unsigned_to_nat(37u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_unreachable_x21___rarg___closed__2;
x_20 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg(x_1, x_16, x_17, x_18, x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_5);
x_23 = lean_apply_1(x_5, x_21);
x_24 = lean_box(x_8);
x_25 = lean_box(x_9);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1___boxed), 12, 11);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_10);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_4);
lean_closure_set(x_26, 6, x_5);
lean_closure_set(x_26, 7, x_6);
lean_closure_set(x_26, 8, x_7);
lean_closure_set(x_26, 9, x_24);
lean_closure_set(x_26, 10, x_25);
x_27 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_26);
return x_27;
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_6);
x_30 = lean_apply_1(x_6, x_28);
x_31 = lean_box(x_8);
x_32 = lean_box(x_9);
lean_inc(x_1);
x_33 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2___boxed), 12, 11);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_10);
lean_closure_set(x_33, 2, x_1);
lean_closure_set(x_33, 3, x_2);
lean_closure_set(x_33, 4, x_3);
lean_closure_set(x_33, 5, x_4);
lean_closure_set(x_33, 6, x_5);
lean_closure_set(x_33, 7, x_6);
lean_closure_set(x_33, 8, x_7);
lean_closure_set(x_33, 9, x_31);
lean_closure_set(x_33, 10, x_32);
x_34 = lean_apply_4(x_29, lean_box(0), lean_box(0), x_30, x_33);
return x_34;
}
case 4:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_36, lean_box(0), x_10);
return x_37;
}
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = l_Lean_Expr_getAppFn___main(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
x_42 = lean_box(x_9);
x_43 = lean_box(x_8);
x_44 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3___boxed), 12, 11);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_1);
lean_closure_set(x_44, 2, x_10);
lean_closure_set(x_44, 3, x_7);
lean_closure_set(x_44, 4, x_42);
lean_closure_set(x_44, 5, x_2);
lean_closure_set(x_44, 6, x_3);
lean_closure_set(x_44, 7, x_4);
lean_closure_set(x_44, 8, x_5);
lean_closure_set(x_44, 9, x_6);
lean_closure_set(x_44, 10, x_43);
x_45 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_41, x_44);
return x_45;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_10, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 3);
lean_inc(x_47);
lean_dec(x_10);
x_48 = lean_expr_instantiate1(x_47, x_46);
lean_dec(x_46);
lean_dec(x_47);
x_10 = x_48;
goto _start;
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_dec(x_10);
x_10 = x_50;
goto _start;
}
case 11:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_10, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_apply_1(x_2, x_53);
lean_inc(x_10);
lean_inc(x_1);
x_56 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_10);
lean_closure_set(x_56, 2, x_7);
lean_closure_set(x_56, 3, x_1);
lean_closure_set(x_56, 4, x_52);
lean_closure_set(x_56, 5, x_10);
x_57 = lean_apply_4(x_54, lean_box(0), lean_box(0), x_55, x_56);
return x_57;
}
default: 
{
lean_object* x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(0);
x_11 = x_58;
goto block_15;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
x_20 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19, x_20, x_18);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_reduceProjectionFnAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_11);
return x_18;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_11__deltaBetaDefinition___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
x_20 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19, x_20, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_19;
}
}
lean_object* l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_reduceQuotRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
x_20 = lean_unbox(x_17);
lean_dec(x_17);
x_21 = l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19, x_20, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_16);
lean_dec(x_16);
x_22 = lean_unbox(x_17);
lean_dec(x_17);
x_23 = l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21, x_22, x_18, x_19, x_20);
return x_23;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_reduceRecAux___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__9(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__10(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__11(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__12(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_panicWithPos___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__14(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_10);
lean_dec(x_10);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
x_15 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_14, x_12);
lean_dec(x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_10);
lean_dec(x_10);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
x_15 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_14, x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
x_15 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_14, x_12);
return x_15;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = l___private_Init_Lean_WHNFUtil_12__whnfCore___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_12__whnfCore___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_WHNFUtil_8__whnfEasyCases___main___at___private_Init_Lean_WHNFUtil_12__whnfCore___main___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = l___private_Init_Lean_WHNFUtil_12__whnfCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
lean_object* l___private_Init_Lean_WHNFUtil_12__whnfCore___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_WHNFUtil_12__whnfCore(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_ProjFns(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_WHNFUtil(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__1);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__2);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__3);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__4);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__5);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__6);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__7);
l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8 = _init_l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_3__toCtorIfLit___closed__8);
l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1 = _init_l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__1);
l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2 = _init_l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2();
lean_mark_persistent(l___private_Init_Lean_WHNFUtil_9__isIdRhsApp___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
