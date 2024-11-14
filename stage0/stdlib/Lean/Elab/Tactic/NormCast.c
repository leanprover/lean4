// Lean compiler output
// Module: Lean.Elab.Tactic.NormCast
// Imports: Lean.Meta.Tactic.NormCast Lean.Elab.Tactic.Conv.Simp Lean.Elab.ElabRules
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2;
extern lean_object* l_Lean_profiler;
static lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2;
static lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19;
static lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3;
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6;
uint8_t lean_float_decLt(double, double);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2;
lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3;
static double l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15;
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2;
static double l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_discharge_x3f_x27___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
static lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6;
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7;
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12;
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2;
lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6;
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_discharge_x3f_x27___spec__7___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4;
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2;
lean_object* l_Lean_Meta_NormCast_addElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3;
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5;
extern lean_object* l_Lean_bombEmoji;
extern lean_object* l_Lean_checkEmoji;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2;
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2;
extern lean_object* l_Lean_Meta_NormCast_pushCastExt;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1;
extern lean_object* l_Lean_trace_profiler_threshold;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3;
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2;
extern lean_object* l_Lean_Meta_NormCast_normCastExt;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_crossEmoji;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3;
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_prove___closed__1;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3;
static double l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7;
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7;
lean_object* lean_array_mk(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2;
lean_object* l_Lean_exceptOptionEmoji___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4;
static lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5;
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_discharge_x3f_x27___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2;
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_cast", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NormCast", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20;
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
x_3 = 0;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_Simp_Result_mkEqSymm(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_Result_mkEqTrans(x_3, x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4;
x_3 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10;
x_3 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9;
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
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4;
x_3 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_12 = 2;
lean_ctor_set_uint8(x_10, 9, x_12);
x_13 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_1);
x_18 = lean_array_mk(x_13);
x_19 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1;
x_20 = l_Lean_Meta_Simp_mkContext(x_19, x_18, x_15, x_4, x_5, x_6, x_7, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13;
x_27 = lean_st_mk_ref(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
lean_inc(x_21);
lean_inc(x_24);
x_30 = lean_simp(x_2, x_24, x_21, x_28, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
lean_inc(x_21);
lean_inc(x_24);
lean_inc(x_3);
x_33 = lean_simp(x_3, x_24, x_21, x_28, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_isExprDefEq(x_36, x_37, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = lean_st_ref_get(x_28, x_41);
lean_dec(x_28);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_box(0);
x_50 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(x_3, x_34, x_31, x_49, x_24, x_21, x_28, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_21);
lean_dec(x_24);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_28, x_52);
lean_dec(x_28);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_28);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_38, 0);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_38);
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
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
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
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_30);
if (x_70 == 0)
{
return x_30;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_30, 0);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_30);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_mk(x_77);
x_79 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1;
x_80 = l_Lean_Meta_Simp_mkContext(x_79, x_78, x_74, x_4, x_5, x_6, x_7, x_75);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13;
x_87 = lean_st_mk_ref(x_86, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_88);
lean_inc(x_81);
lean_inc(x_84);
x_90 = lean_simp(x_2, x_84, x_81, x_88, x_4, x_5, x_6, x_7, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_88);
lean_inc(x_81);
lean_inc(x_84);
lean_inc(x_3);
x_93 = lean_simp(x_3, x_84, x_81, x_88, x_4, x_5, x_6, x_7, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_Meta_isExprDefEq(x_96, x_97, x_4, x_5, x_6, x_7, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
x_103 = lean_st_ref_get(x_88, x_101);
lean_dec(x_88);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_dec(x_98);
x_108 = lean_box(0);
x_109 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(x_3, x_94, x_91, x_108, x_84, x_81, x_88, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_81);
lean_dec(x_84);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_st_ref_get(x_88, x_111);
lean_dec(x_88);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_88);
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_120 = lean_ctor_get(x_98, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_98, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_122 = x_98;
} else {
 lean_dec_ref(x_98);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_124 = lean_ctor_get(x_93, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_93, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_126 = x_93;
} else {
 lean_dec_ref(x_93);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_128 = lean_ctor_get(x_90, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_90, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_130 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_132 = lean_ctor_get_uint8(x_10, 0);
x_133 = lean_ctor_get_uint8(x_10, 1);
x_134 = lean_ctor_get_uint8(x_10, 2);
x_135 = lean_ctor_get_uint8(x_10, 3);
x_136 = lean_ctor_get_uint8(x_10, 4);
x_137 = lean_ctor_get_uint8(x_10, 5);
x_138 = lean_ctor_get_uint8(x_10, 6);
x_139 = lean_ctor_get_uint8(x_10, 7);
x_140 = lean_ctor_get_uint8(x_10, 8);
x_141 = lean_ctor_get_uint8(x_10, 10);
x_142 = lean_ctor_get_uint8(x_10, 11);
x_143 = lean_ctor_get_uint8(x_10, 12);
lean_dec(x_10);
x_144 = 2;
x_145 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_145, 0, x_132);
lean_ctor_set_uint8(x_145, 1, x_133);
lean_ctor_set_uint8(x_145, 2, x_134);
lean_ctor_set_uint8(x_145, 3, x_135);
lean_ctor_set_uint8(x_145, 4, x_136);
lean_ctor_set_uint8(x_145, 5, x_137);
lean_ctor_set_uint8(x_145, 6, x_138);
lean_ctor_set_uint8(x_145, 7, x_139);
lean_ctor_set_uint8(x_145, 8, x_140);
lean_ctor_set_uint8(x_145, 9, x_144);
lean_ctor_set_uint8(x_145, 10, x_141);
lean_ctor_set_uint8(x_145, 11, x_142);
lean_ctor_set_uint8(x_145, 12, x_143);
lean_ctor_set(x_4, 0, x_145);
x_146 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_8);
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
x_150 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_149;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_mk(x_151);
x_153 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1;
x_154 = l_Lean_Meta_Simp_mkContext(x_153, x_152, x_147, x_4, x_5, x_6, x_7, x_148);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13;
x_161 = lean_st_mk_ref(x_160, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_162);
lean_inc(x_155);
lean_inc(x_158);
x_164 = lean_simp(x_2, x_158, x_155, x_162, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_162);
lean_inc(x_155);
lean_inc(x_158);
lean_inc(x_3);
x_167 = lean_simp(x_3, x_158, x_155, x_162, x_4, x_5, x_6, x_7, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_172 = l_Lean_Meta_isExprDefEq(x_170, x_171, x_4, x_5, x_6, x_7, x_169);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_box(0);
x_177 = lean_st_ref_get(x_162, x_175);
lean_dec(x_162);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
lean_dec(x_172);
x_182 = lean_box(0);
x_183 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(x_3, x_168, x_165, x_182, x_158, x_155, x_162, x_4, x_5, x_6, x_7, x_181);
lean_dec(x_155);
lean_dec(x_158);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_st_ref_get(x_162, x_185);
lean_dec(x_162);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_162);
x_190 = lean_ctor_get(x_183, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_183, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_192 = x_183;
} else {
 lean_dec_ref(x_183);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_194 = lean_ctor_get(x_172, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_172, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_196 = x_172;
} else {
 lean_dec_ref(x_172);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_165);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_198 = lean_ctor_get(x_167, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_167, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_200 = x_167;
} else {
 lean_dec_ref(x_167);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_4);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_202 = lean_ctor_get(x_164, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_164, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_204 = x_164;
} else {
 lean_dec_ref(x_164);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_206 = lean_ctor_get(x_4, 0);
x_207 = lean_ctor_get(x_4, 1);
x_208 = lean_ctor_get(x_4, 2);
x_209 = lean_ctor_get(x_4, 3);
x_210 = lean_ctor_get(x_4, 4);
x_211 = lean_ctor_get(x_4, 5);
x_212 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_213 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_4);
x_214 = lean_ctor_get_uint8(x_206, 0);
x_215 = lean_ctor_get_uint8(x_206, 1);
x_216 = lean_ctor_get_uint8(x_206, 2);
x_217 = lean_ctor_get_uint8(x_206, 3);
x_218 = lean_ctor_get_uint8(x_206, 4);
x_219 = lean_ctor_get_uint8(x_206, 5);
x_220 = lean_ctor_get_uint8(x_206, 6);
x_221 = lean_ctor_get_uint8(x_206, 7);
x_222 = lean_ctor_get_uint8(x_206, 8);
x_223 = lean_ctor_get_uint8(x_206, 10);
x_224 = lean_ctor_get_uint8(x_206, 11);
x_225 = lean_ctor_get_uint8(x_206, 12);
if (lean_is_exclusive(x_206)) {
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
 x_226 = lean_box(0);
}
x_227 = 2;
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 0, 13);
} else {
 x_228 = x_226;
}
lean_ctor_set_uint8(x_228, 0, x_214);
lean_ctor_set_uint8(x_228, 1, x_215);
lean_ctor_set_uint8(x_228, 2, x_216);
lean_ctor_set_uint8(x_228, 3, x_217);
lean_ctor_set_uint8(x_228, 4, x_218);
lean_ctor_set_uint8(x_228, 5, x_219);
lean_ctor_set_uint8(x_228, 6, x_220);
lean_ctor_set_uint8(x_228, 7, x_221);
lean_ctor_set_uint8(x_228, 8, x_222);
lean_ctor_set_uint8(x_228, 9, x_227);
lean_ctor_set_uint8(x_228, 10, x_223);
lean_ctor_set_uint8(x_228, 11, x_224);
lean_ctor_set_uint8(x_228, 12, x_225);
x_229 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_207);
lean_ctor_set(x_229, 2, x_208);
lean_ctor_set(x_229, 3, x_209);
lean_ctor_set(x_229, 4, x_210);
lean_ctor_set(x_229, 5, x_211);
lean_ctor_set_uint8(x_229, sizeof(void*)*6, x_212);
lean_ctor_set_uint8(x_229, sizeof(void*)*6 + 1, x_213);
x_230 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_8);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_233;
 lean_ctor_set_tag(x_235, 1);
}
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_array_mk(x_235);
x_237 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1;
x_238 = l_Lean_Meta_Simp_mkContext(x_237, x_236, x_231, x_229, x_5, x_6, x_7, x_232);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13;
x_245 = lean_st_mk_ref(x_244, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_229);
lean_inc(x_246);
lean_inc(x_239);
lean_inc(x_242);
x_248 = lean_simp(x_2, x_242, x_239, x_246, x_229, x_5, x_6, x_7, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_229);
lean_inc(x_246);
lean_inc(x_239);
lean_inc(x_242);
lean_inc(x_3);
x_251 = lean_simp(x_3, x_242, x_239, x_246, x_229, x_5, x_6, x_7, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_249, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_229);
x_256 = l_Lean_Meta_isExprDefEq(x_254, x_255, x_229, x_5, x_6, x_7, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_box(0);
x_261 = lean_st_ref_get(x_246, x_259);
lean_dec(x_246);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_260);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_256, 1);
lean_inc(x_265);
lean_dec(x_256);
x_266 = lean_box(0);
x_267 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(x_3, x_252, x_249, x_266, x_242, x_239, x_246, x_229, x_5, x_6, x_7, x_265);
lean_dec(x_239);
lean_dec(x_242);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_st_ref_get(x_246, x_269);
lean_dec(x_246);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_268);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_246);
x_274 = lean_ctor_get(x_267, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_267, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_276 = x_267;
} else {
 lean_dec_ref(x_267);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_278 = lean_ctor_get(x_256, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_256, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_280 = x_256;
} else {
 lean_dec_ref(x_256);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_251, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_251, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_284 = x_251;
} else {
 lean_dec_ref(x_251);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_246);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_286 = lean_ctor_get(x_248, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_248, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_288 = x_248;
} else {
 lean_dec_ref(x_248);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_1, x_5, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_4, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_9);
return x_14;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, double x_9, double x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
double x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_19);
if (x_20 == 0)
{
if (x_8 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_18, x_21, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_2);
x_24 = lean_box(0);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_23, x_24, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_2);
x_27 = lean_box(0);
x_28 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_26, x_27, x_12, x_13, x_14, x_15, x_16);
return x_28;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_18 = lean_apply_6(x_10, x_5, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_19, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2;
x_24 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_23, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_24;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_io_mono_nanos_now(x_16);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_90 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_89);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_io_mono_nanos_now(x_93);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; double x_101; double x_102; double x_103; double x_104; double x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = 0;
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Float_ofScientific(x_88, x_99, x_100);
lean_dec(x_88);
x_102 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_103 = lean_float_div(x_101, x_102);
x_104 = l_Float_ofScientific(x_97, x_99, x_100);
lean_dec(x_97);
x_105 = lean_float_div(x_104, x_102);
x_106 = lean_box_float(x_103);
x_107 = lean_box_float(x_105);
lean_ctor_set(x_95, 1, x_107);
lean_ctor_set(x_95, 0, x_106);
lean_ctor_set(x_90, 1, x_95);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_98;
goto block_86;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; double x_112; double x_113; double x_114; double x_115; double x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_95, 0);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_95);
x_110 = 0;
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Float_ofScientific(x_88, x_110, x_111);
lean_dec(x_88);
x_113 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_114 = lean_float_div(x_112, x_113);
x_115 = l_Float_ofScientific(x_108, x_110, x_111);
lean_dec(x_108);
x_116 = lean_float_div(x_115, x_113);
x_117 = lean_box_float(x_114);
x_118 = lean_box_float(x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_90, 1, x_119);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_109;
goto block_86;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; double x_129; double x_130; double x_131; double x_132; double x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_io_mono_nanos_now(x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = 0;
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Float_ofScientific(x_88, x_127, x_128);
lean_dec(x_88);
x_130 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_131 = lean_float_div(x_129, x_130);
x_132 = l_Float_ofScientific(x_124, x_127, x_128);
lean_dec(x_124);
x_133 = lean_float_div(x_132, x_130);
x_134 = lean_box_float(x_131);
x_135 = lean_box_float(x_133);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_136);
x_19 = x_137;
x_20 = x_125;
goto block_86;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_90);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_90, 0);
x_140 = lean_ctor_get(x_90, 1);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_139);
x_142 = lean_io_mono_nanos_now(x_140);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; double x_148; double x_149; double x_150; double x_151; double x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
x_146 = 0;
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Float_ofScientific(x_88, x_146, x_147);
lean_dec(x_88);
x_149 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_150 = lean_float_div(x_148, x_149);
x_151 = l_Float_ofScientific(x_144, x_146, x_147);
lean_dec(x_144);
x_152 = lean_float_div(x_151, x_149);
x_153 = lean_box_float(x_150);
x_154 = lean_box_float(x_152);
lean_ctor_set(x_142, 1, x_154);
lean_ctor_set(x_142, 0, x_153);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_142);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_145;
goto block_86;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; double x_159; double x_160; double x_161; double x_162; double x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_142, 0);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_142);
x_157 = 0;
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Float_ofScientific(x_88, x_157, x_158);
lean_dec(x_88);
x_160 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_161 = lean_float_div(x_159, x_160);
x_162 = l_Float_ofScientific(x_155, x_157, x_158);
lean_dec(x_155);
x_163 = lean_float_div(x_162, x_160);
x_164 = lean_box_float(x_161);
x_165 = lean_box_float(x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_166);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_156;
goto block_86;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; double x_176; double x_177; double x_178; double x_179; double x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_167 = lean_ctor_get(x_90, 0);
x_168 = lean_ctor_get(x_90, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_90);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_io_mono_nanos_now(x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = 0;
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Float_ofScientific(x_88, x_174, x_175);
lean_dec(x_88);
x_177 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_178 = lean_float_div(x_176, x_177);
x_179 = l_Float_ofScientific(x_171, x_174, x_175);
lean_dec(x_171);
x_180 = lean_float_div(x_179, x_177);
x_181 = lean_box_float(x_178);
x_182 = lean_box_float(x_180);
if (lean_is_scalar(x_173)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_173;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_169);
lean_ctor_set(x_184, 1, x_183);
x_19 = x_184;
x_20 = x_172;
goto block_86;
}
}
block_86:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_72; uint8_t x_73; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_72 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_73 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_25 = x_74;
goto block_71;
}
else
{
double x_75; double x_76; double x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; double x_82; double x_83; double x_84; uint8_t x_85; 
x_75 = lean_unbox_float(x_24);
x_76 = lean_unbox_float(x_23);
x_77 = lean_float_sub(x_75, x_76);
x_78 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_79 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_78);
x_80 = 0;
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Float_ofScientific(x_79, x_80, x_81);
lean_dec(x_79);
x_83 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4;
x_84 = lean_float_div(x_82, x_83);
x_85 = lean_float_decLt(x_84, x_77);
x_25 = x_85;
goto block_71;
}
block_71:
{
if (x_6 == 0)
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_12, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 3);
x_31 = l_Lean_PersistentArray_append___rarg(x_15, x_30);
lean_dec(x_30);
lean_ctor_set(x_27, 3, x_31);
x_32 = lean_st_ref_set(x_12, x_27, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_22, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
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
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
x_45 = lean_ctor_get(x_27, 2);
x_46 = lean_ctor_get(x_27, 3);
x_47 = lean_ctor_get(x_27, 4);
x_48 = lean_ctor_get(x_27, 5);
x_49 = lean_ctor_get(x_27, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_50 = l_Lean_PersistentArray_append___rarg(x_15, x_46);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
x_52 = lean_st_ref_set(x_12, x_51, x_28);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_22, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_63; double x_64; double x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_unbox_float(x_23);
lean_dec(x_23);
x_65 = lean_unbox_float(x_24);
lean_dec(x_24);
x_66 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_64, x_65, x_5, x_63, x_9, x_10, x_11, x_12, x_20);
return x_66;
}
}
else
{
lean_object* x_67; double x_68; double x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = lean_unbox_float(x_23);
lean_dec(x_23);
x_69 = lean_unbox_float(x_24);
lean_dec(x_24);
x_70 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_68, x_69, x_5, x_67, x_9, x_10, x_11, x_12, x_20);
return x_70;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_io_get_num_heartbeats(x_16);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_254 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_253);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_256);
x_259 = lean_io_get_num_heartbeats(x_257);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; double x_265; double x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_259, 1);
x_263 = 0;
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Float_ofScientific(x_252, x_263, x_264);
lean_dec(x_252);
x_266 = l_Float_ofScientific(x_261, x_263, x_264);
lean_dec(x_261);
x_267 = lean_box_float(x_265);
x_268 = lean_box_float(x_266);
lean_ctor_set(x_259, 1, x_268);
lean_ctor_set(x_259, 0, x_267);
lean_ctor_set(x_254, 1, x_259);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_262;
goto block_250;
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; double x_273; double x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_269 = lean_ctor_get(x_259, 0);
x_270 = lean_ctor_get(x_259, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_259);
x_271 = 0;
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Float_ofScientific(x_252, x_271, x_272);
lean_dec(x_252);
x_274 = l_Float_ofScientific(x_269, x_271, x_272);
lean_dec(x_269);
x_275 = lean_box_float(x_273);
x_276 = lean_box_float(x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_254, 1, x_277);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_270;
goto block_250;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; double x_287; double x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_278 = lean_ctor_get(x_254, 0);
x_279 = lean_ctor_get(x_254, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_254);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_278);
x_281 = lean_io_get_num_heartbeats(x_279);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = 0;
x_286 = lean_unsigned_to_nat(0u);
x_287 = l_Float_ofScientific(x_252, x_285, x_286);
lean_dec(x_252);
x_288 = l_Float_ofScientific(x_282, x_285, x_286);
lean_dec(x_282);
x_289 = lean_box_float(x_287);
x_290 = lean_box_float(x_288);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_280);
lean_ctor_set(x_292, 1, x_291);
x_185 = x_292;
x_186 = x_283;
goto block_250;
}
}
else
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_254);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_254, 0);
x_295 = lean_ctor_get(x_254, 1);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_294);
x_297 = lean_io_get_num_heartbeats(x_295);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; double x_303; double x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = 0;
x_302 = lean_unsigned_to_nat(0u);
x_303 = l_Float_ofScientific(x_252, x_301, x_302);
lean_dec(x_252);
x_304 = l_Float_ofScientific(x_299, x_301, x_302);
lean_dec(x_299);
x_305 = lean_box_float(x_303);
x_306 = lean_box_float(x_304);
lean_ctor_set(x_297, 1, x_306);
lean_ctor_set(x_297, 0, x_305);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_297);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_300;
goto block_250;
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; double x_311; double x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_307 = lean_ctor_get(x_297, 0);
x_308 = lean_ctor_get(x_297, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_297);
x_309 = 0;
x_310 = lean_unsigned_to_nat(0u);
x_311 = l_Float_ofScientific(x_252, x_309, x_310);
lean_dec(x_252);
x_312 = l_Float_ofScientific(x_307, x_309, x_310);
lean_dec(x_307);
x_313 = lean_box_float(x_311);
x_314 = lean_box_float(x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_315);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_308;
goto block_250;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; double x_325; double x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_316 = lean_ctor_get(x_254, 0);
x_317 = lean_ctor_get(x_254, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_254);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_319 = lean_io_get_num_heartbeats(x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
x_323 = 0;
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Float_ofScientific(x_252, x_323, x_324);
lean_dec(x_252);
x_326 = l_Float_ofScientific(x_320, x_323, x_324);
lean_dec(x_320);
x_327 = lean_box_float(x_325);
x_328 = lean_box_float(x_326);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_318);
lean_ctor_set(x_330, 1, x_329);
x_185 = x_330;
x_186 = x_321;
goto block_250;
}
}
block_250:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_238; uint8_t x_239; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_238 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_239 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 0;
x_191 = x_240;
goto block_237;
}
else
{
double x_241; double x_242; double x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; double x_248; uint8_t x_249; 
x_241 = lean_unbox_float(x_190);
x_242 = lean_unbox_float(x_189);
x_243 = lean_float_sub(x_241, x_242);
x_244 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_245 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_244);
x_246 = 0;
x_247 = lean_unsigned_to_nat(0u);
x_248 = l_Float_ofScientific(x_245, x_246, x_247);
lean_dec(x_245);
x_249 = lean_float_decLt(x_248, x_243);
x_191 = x_249;
goto block_237;
}
block_237:
{
if (x_6 == 0)
{
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_st_ref_take(x_12, x_186);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_193, 3);
x_197 = l_Lean_PersistentArray_append___rarg(x_15, x_196);
lean_dec(x_196);
lean_ctor_set(x_193, 3, x_197);
x_198 = lean_st_ref_set(x_12, x_193, x_194);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_188, x_9, x_10, x_11, x_12, x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
return x_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_200);
if (x_205 == 0)
{
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_200, 0);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_200);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_193, 0);
x_210 = lean_ctor_get(x_193, 1);
x_211 = lean_ctor_get(x_193, 2);
x_212 = lean_ctor_get(x_193, 3);
x_213 = lean_ctor_get(x_193, 4);
x_214 = lean_ctor_get(x_193, 5);
x_215 = lean_ctor_get(x_193, 6);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_193);
x_216 = l_Lean_PersistentArray_append___rarg(x_15, x_212);
lean_dec(x_212);
x_217 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_210);
lean_ctor_set(x_217, 2, x_211);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_217, 4, x_213);
lean_ctor_set(x_217, 5, x_214);
lean_ctor_set(x_217, 6, x_215);
x_218 = lean_st_ref_set(x_12, x_217, x_194);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_188, x_9, x_10, x_11, x_12, x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
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
lean_object* x_229; double x_230; double x_231; lean_object* x_232; 
x_229 = lean_box(0);
x_230 = lean_unbox_float(x_189);
lean_dec(x_189);
x_231 = lean_unbox_float(x_190);
lean_dec(x_190);
x_232 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_230, x_231, x_5, x_229, x_9, x_10, x_11, x_12, x_186);
return x_232;
}
}
else
{
lean_object* x_233; double x_234; double x_235; lean_object* x_236; 
x_233 = lean_box(0);
x_234 = lean_unbox_float(x_189);
lean_dec(x_189);
x_235 = lean_unbox_float(x_190);
lean_dec(x_190);
x_236 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_234, x_235, x_5, x_233, x_9, x_10, x_11, x_12, x_186);
return x_236;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_17 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
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
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_13);
lean_dec(x_13);
x_29 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4(x_11, x_1, x_4, x_5, x_2, x_28, x_3, x_27, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_11);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_unbox(x_13);
lean_dec(x_13);
x_33 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4(x_11, x_1, x_4, x_5, x_2, x_32, x_3, x_31, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_11);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" proving: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_11);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Lean_exceptOptionEmoji___rarg(x_3);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_21);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
else
{
uint8_t x_33; 
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Tactic_NormCast_proveEqUsing(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___boxed), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_Meta_NormCast_normCastExt;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2___boxed), 8, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
x_12 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
x_13 = 1;
x_14 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
x_15 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1(x_12, x_8, x_11, x_13, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox_float(x_9);
lean_dec(x_9);
x_20 = lean_unbox_float(x_10);
lean_dec(x_10);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox_float(x_8);
lean_dec(x_8);
x_20 = lean_unbox_float(x_9);
lean_dec(x_9);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3(x_1, x_17, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_coerce_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_18 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1;
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_getCoeFnInfo_x3f(x_9, x_4, x_5, x_6);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_apply_6(x_7, x_13, x_2, x_3, x_4, x_5, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_free_object(x_11);
lean_dec(x_19);
lean_free_object(x_10);
x_24 = lean_box(0);
x_25 = lean_apply_6(x_7, x_24, x_2, x_3, x_4, x_5, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_nat_sub(x_21, x_26);
lean_dec(x_26);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Expr_getRevArg_x21(x_1, x_29);
lean_ctor_set(x_11, 0, x_30);
return x_10;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_32);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_31);
lean_free_object(x_10);
x_36 = lean_box(0);
x_37 = lean_apply_6(x_7, x_36, x_2, x_3, x_4, x_5, x_16);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_nat_sub(x_33, x_38);
lean_dec(x_38);
lean_dec(x_33);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_39, x_40);
lean_dec(x_39);
x_42 = l_Lean_Expr_getRevArg_x21(x_1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_10, 0, x_43);
return x_10;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_46 = x_11;
} else {
 lean_dec_ref(x_11);
 x_46 = lean_box(0);
}
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_47);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
x_51 = lean_box(0);
x_52 = lean_apply_6(x_7, x_51, x_2, x_3, x_4, x_5, x_44);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_nat_sub(x_48, x_53);
lean_dec(x_53);
lean_dec(x_48);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_54, x_55);
lean_dec(x_54);
x_57 = l_Lean_Expr_getRevArg_x21(x_1, x_56);
if (lean_is_scalar(x_46)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_46;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_8);
x_60 = lean_box(0);
x_61 = lean_apply_6(x_7, x_60, x_2, x_3, x_4, x_5, x_6);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1;
x_2 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5;
x_18 = lean_string_dec_eq(x_12, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box(0);
return x_19;
}
else
{
if (lean_obj_tag(x_10) == 9)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_11);
x_27 = lean_box(0);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
x_28 = lean_box(0);
return x_28;
}
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_box(0);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
x_33 = lean_box(0);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_4);
x_34 = lean_box(0);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_box(0);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9;
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_9);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_1, x_5, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_4, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, double x_9, double x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
double x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_19);
if (x_20 == 0)
{
if (x_8 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_18, x_21, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_2);
x_24 = lean_box(0);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_23, x_24, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_2);
x_27 = lean_box(0);
x_28 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(x_4, x_5, x_11, x_6, x_26, x_27, x_12, x_13, x_14, x_15, x_16);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_18 = lean_apply_6(x_10, x_5, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_19, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2;
x_24 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_23, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_io_mono_nanos_now(x_16);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_90 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_89);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_io_mono_nanos_now(x_93);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; double x_101; double x_102; double x_103; double x_104; double x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = 0;
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Float_ofScientific(x_88, x_99, x_100);
lean_dec(x_88);
x_102 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_103 = lean_float_div(x_101, x_102);
x_104 = l_Float_ofScientific(x_97, x_99, x_100);
lean_dec(x_97);
x_105 = lean_float_div(x_104, x_102);
x_106 = lean_box_float(x_103);
x_107 = lean_box_float(x_105);
lean_ctor_set(x_95, 1, x_107);
lean_ctor_set(x_95, 0, x_106);
lean_ctor_set(x_90, 1, x_95);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_98;
goto block_86;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; double x_112; double x_113; double x_114; double x_115; double x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_95, 0);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_95);
x_110 = 0;
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Float_ofScientific(x_88, x_110, x_111);
lean_dec(x_88);
x_113 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_114 = lean_float_div(x_112, x_113);
x_115 = l_Float_ofScientific(x_108, x_110, x_111);
lean_dec(x_108);
x_116 = lean_float_div(x_115, x_113);
x_117 = lean_box_float(x_114);
x_118 = lean_box_float(x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_90, 1, x_119);
lean_ctor_set(x_90, 0, x_94);
x_19 = x_90;
x_20 = x_109;
goto block_86;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; double x_129; double x_130; double x_131; double x_132; double x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_io_mono_nanos_now(x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = 0;
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Float_ofScientific(x_88, x_127, x_128);
lean_dec(x_88);
x_130 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_131 = lean_float_div(x_129, x_130);
x_132 = l_Float_ofScientific(x_124, x_127, x_128);
lean_dec(x_124);
x_133 = lean_float_div(x_132, x_130);
x_134 = lean_box_float(x_131);
x_135 = lean_box_float(x_133);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_136);
x_19 = x_137;
x_20 = x_125;
goto block_86;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_90);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_90, 0);
x_140 = lean_ctor_get(x_90, 1);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_139);
x_142 = lean_io_mono_nanos_now(x_140);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; double x_148; double x_149; double x_150; double x_151; double x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
x_146 = 0;
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Float_ofScientific(x_88, x_146, x_147);
lean_dec(x_88);
x_149 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_150 = lean_float_div(x_148, x_149);
x_151 = l_Float_ofScientific(x_144, x_146, x_147);
lean_dec(x_144);
x_152 = lean_float_div(x_151, x_149);
x_153 = lean_box_float(x_150);
x_154 = lean_box_float(x_152);
lean_ctor_set(x_142, 1, x_154);
lean_ctor_set(x_142, 0, x_153);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_142);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_145;
goto block_86;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; double x_159; double x_160; double x_161; double x_162; double x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_142, 0);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_142);
x_157 = 0;
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Float_ofScientific(x_88, x_157, x_158);
lean_dec(x_88);
x_160 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_161 = lean_float_div(x_159, x_160);
x_162 = l_Float_ofScientific(x_155, x_157, x_158);
lean_dec(x_155);
x_163 = lean_float_div(x_162, x_160);
x_164 = lean_box_float(x_161);
x_165 = lean_box_float(x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 1, x_166);
lean_ctor_set(x_90, 0, x_141);
x_19 = x_90;
x_20 = x_156;
goto block_86;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; double x_176; double x_177; double x_178; double x_179; double x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_167 = lean_ctor_get(x_90, 0);
x_168 = lean_ctor_get(x_90, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_90);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_io_mono_nanos_now(x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = 0;
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Float_ofScientific(x_88, x_174, x_175);
lean_dec(x_88);
x_177 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_178 = lean_float_div(x_176, x_177);
x_179 = l_Float_ofScientific(x_171, x_174, x_175);
lean_dec(x_171);
x_180 = lean_float_div(x_179, x_177);
x_181 = lean_box_float(x_178);
x_182 = lean_box_float(x_180);
if (lean_is_scalar(x_173)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_173;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_169);
lean_ctor_set(x_184, 1, x_183);
x_19 = x_184;
x_20 = x_172;
goto block_86;
}
}
block_86:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_72; uint8_t x_73; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_72 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_73 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_25 = x_74;
goto block_71;
}
else
{
double x_75; double x_76; double x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; double x_82; double x_83; double x_84; uint8_t x_85; 
x_75 = lean_unbox_float(x_24);
x_76 = lean_unbox_float(x_23);
x_77 = lean_float_sub(x_75, x_76);
x_78 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_79 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_78);
x_80 = 0;
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Float_ofScientific(x_79, x_80, x_81);
lean_dec(x_79);
x_83 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4;
x_84 = lean_float_div(x_82, x_83);
x_85 = lean_float_decLt(x_84, x_77);
x_25 = x_85;
goto block_71;
}
block_71:
{
if (x_6 == 0)
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_12, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 3);
x_31 = l_Lean_PersistentArray_append___rarg(x_15, x_30);
lean_dec(x_30);
lean_ctor_set(x_27, 3, x_31);
x_32 = lean_st_ref_set(x_12, x_27, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_22, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
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
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
x_45 = lean_ctor_get(x_27, 2);
x_46 = lean_ctor_get(x_27, 3);
x_47 = lean_ctor_get(x_27, 4);
x_48 = lean_ctor_get(x_27, 5);
x_49 = lean_ctor_get(x_27, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_50 = l_Lean_PersistentArray_append___rarg(x_15, x_46);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
x_52 = lean_st_ref_set(x_12, x_51, x_28);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_22, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_22);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_63; double x_64; double x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_unbox_float(x_23);
lean_dec(x_23);
x_65 = lean_unbox_float(x_24);
lean_dec(x_24);
x_66 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_64, x_65, x_5, x_63, x_9, x_10, x_11, x_12, x_20);
return x_66;
}
}
else
{
lean_object* x_67; double x_68; double x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = lean_unbox_float(x_23);
lean_dec(x_23);
x_69 = lean_unbox_float(x_24);
lean_dec(x_24);
x_70 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_22, x_1, x_25, x_68, x_69, x_5, x_67, x_9, x_10, x_11, x_12, x_20);
return x_70;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_io_get_num_heartbeats(x_16);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_254 = lean_apply_5(x_7, x_9, x_10, x_11, x_12, x_253);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_256);
x_259 = lean_io_get_num_heartbeats(x_257);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; double x_265; double x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_259, 1);
x_263 = 0;
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Float_ofScientific(x_252, x_263, x_264);
lean_dec(x_252);
x_266 = l_Float_ofScientific(x_261, x_263, x_264);
lean_dec(x_261);
x_267 = lean_box_float(x_265);
x_268 = lean_box_float(x_266);
lean_ctor_set(x_259, 1, x_268);
lean_ctor_set(x_259, 0, x_267);
lean_ctor_set(x_254, 1, x_259);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_262;
goto block_250;
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; double x_273; double x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_269 = lean_ctor_get(x_259, 0);
x_270 = lean_ctor_get(x_259, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_259);
x_271 = 0;
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Float_ofScientific(x_252, x_271, x_272);
lean_dec(x_252);
x_274 = l_Float_ofScientific(x_269, x_271, x_272);
lean_dec(x_269);
x_275 = lean_box_float(x_273);
x_276 = lean_box_float(x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_254, 1, x_277);
lean_ctor_set(x_254, 0, x_258);
x_185 = x_254;
x_186 = x_270;
goto block_250;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; double x_287; double x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_278 = lean_ctor_get(x_254, 0);
x_279 = lean_ctor_get(x_254, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_254);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_278);
x_281 = lean_io_get_num_heartbeats(x_279);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = 0;
x_286 = lean_unsigned_to_nat(0u);
x_287 = l_Float_ofScientific(x_252, x_285, x_286);
lean_dec(x_252);
x_288 = l_Float_ofScientific(x_282, x_285, x_286);
lean_dec(x_282);
x_289 = lean_box_float(x_287);
x_290 = lean_box_float(x_288);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_280);
lean_ctor_set(x_292, 1, x_291);
x_185 = x_292;
x_186 = x_283;
goto block_250;
}
}
else
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_254);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_254, 0);
x_295 = lean_ctor_get(x_254, 1);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_294);
x_297 = lean_io_get_num_heartbeats(x_295);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; double x_303; double x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = 0;
x_302 = lean_unsigned_to_nat(0u);
x_303 = l_Float_ofScientific(x_252, x_301, x_302);
lean_dec(x_252);
x_304 = l_Float_ofScientific(x_299, x_301, x_302);
lean_dec(x_299);
x_305 = lean_box_float(x_303);
x_306 = lean_box_float(x_304);
lean_ctor_set(x_297, 1, x_306);
lean_ctor_set(x_297, 0, x_305);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_297);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_300;
goto block_250;
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; double x_311; double x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_307 = lean_ctor_get(x_297, 0);
x_308 = lean_ctor_get(x_297, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_297);
x_309 = 0;
x_310 = lean_unsigned_to_nat(0u);
x_311 = l_Float_ofScientific(x_252, x_309, x_310);
lean_dec(x_252);
x_312 = l_Float_ofScientific(x_307, x_309, x_310);
lean_dec(x_307);
x_313 = lean_box_float(x_311);
x_314 = lean_box_float(x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_tag(x_254, 0);
lean_ctor_set(x_254, 1, x_315);
lean_ctor_set(x_254, 0, x_296);
x_185 = x_254;
x_186 = x_308;
goto block_250;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; double x_325; double x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_316 = lean_ctor_get(x_254, 0);
x_317 = lean_ctor_get(x_254, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_254);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_319 = lean_io_get_num_heartbeats(x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
x_323 = 0;
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Float_ofScientific(x_252, x_323, x_324);
lean_dec(x_252);
x_326 = l_Float_ofScientific(x_320, x_323, x_324);
lean_dec(x_320);
x_327 = lean_box_float(x_325);
x_328 = lean_box_float(x_326);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_318);
lean_ctor_set(x_330, 1, x_329);
x_185 = x_330;
x_186 = x_321;
goto block_250;
}
}
block_250:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_238; uint8_t x_239; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_238 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_239 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 0;
x_191 = x_240;
goto block_237;
}
else
{
double x_241; double x_242; double x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; double x_248; uint8_t x_249; 
x_241 = lean_unbox_float(x_190);
x_242 = lean_unbox_float(x_189);
x_243 = lean_float_sub(x_241, x_242);
x_244 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_245 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_244);
x_246 = 0;
x_247 = lean_unsigned_to_nat(0u);
x_248 = l_Float_ofScientific(x_245, x_246, x_247);
lean_dec(x_245);
x_249 = lean_float_decLt(x_248, x_243);
x_191 = x_249;
goto block_237;
}
block_237:
{
if (x_6 == 0)
{
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_st_ref_take(x_12, x_186);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_193, 3);
x_197 = l_Lean_PersistentArray_append___rarg(x_15, x_196);
lean_dec(x_196);
lean_ctor_set(x_193, 3, x_197);
x_198 = lean_st_ref_set(x_12, x_193, x_194);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_188, x_9, x_10, x_11, x_12, x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
return x_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_200);
if (x_205 == 0)
{
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_200, 0);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_200);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_193, 0);
x_210 = lean_ctor_get(x_193, 1);
x_211 = lean_ctor_get(x_193, 2);
x_212 = lean_ctor_get(x_193, 3);
x_213 = lean_ctor_get(x_193, 4);
x_214 = lean_ctor_get(x_193, 5);
x_215 = lean_ctor_get(x_193, 6);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_193);
x_216 = l_Lean_PersistentArray_append___rarg(x_15, x_212);
lean_dec(x_212);
x_217 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_210);
lean_ctor_set(x_217, 2, x_211);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_217, 4, x_213);
lean_ctor_set(x_217, 5, x_214);
lean_ctor_set(x_217, 6, x_215);
x_218 = lean_st_ref_set(x_12, x_217, x_194);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_188, x_9, x_10, x_11, x_12, x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_188);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
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
lean_object* x_229; double x_230; double x_231; lean_object* x_232; 
x_229 = lean_box(0);
x_230 = lean_unbox_float(x_189);
lean_dec(x_189);
x_231 = lean_unbox_float(x_190);
lean_dec(x_190);
x_232 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_230, x_231, x_5, x_229, x_9, x_10, x_11, x_12, x_186);
return x_232;
}
}
else
{
lean_object* x_233; double x_234; double x_235; lean_object* x_236; 
x_233 = lean_box(0);
x_234 = lean_unbox_float(x_189);
lean_dec(x_189);
x_235 = lean_unbox_float(x_190);
lean_dec(x_190);
x_236 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(x_2, x_3, x_4, x_15, x_188, x_1, x_191, x_234, x_235, x_5, x_233, x_9, x_10, x_11, x_12, x_186);
return x_236;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_17 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
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
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_13);
lean_dec(x_13);
x_29 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4(x_11, x_1, x_4, x_5, x_2, x_28, x_3, x_27, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_11);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_unbox(x_13);
lean_dec(x_13);
x_33 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4(x_11, x_1, x_4, x_5, x_2, x_32, x_3, x_31, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_11);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_bombEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_checkEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_crossEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_10 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1;
lean_inc(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_expr_eqv(x_18, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4;
lean_inc(x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofExpr(x_18);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
x_31 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7;
lean_inc(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_43; lean_object* x_44; lean_object* x_58; lean_object* x_59; lean_object* x_70; lean_object* x_71; lean_object* x_139; lean_object* x_140; lean_object* x_204; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_204 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_208 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_207, x_6, x_7, x_8, x_9, x_206);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_139 = x_209;
x_140 = x_210;
goto block_203;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_ctor_get(x_205, 0);
lean_inc(x_212);
lean_dec(x_205);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_213 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_3, x_6, x_7, x_8, x_9, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_217 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_216, x_6, x_7, x_8, x_9, x_215);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_139 = x_218;
x_140 = x_219;
goto block_203;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
lean_dec(x_213);
x_221 = lean_ctor_get(x_214, 0);
lean_inc(x_221);
lean_dec(x_214);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_212);
x_222 = lean_infer_type(x_212, x_6, x_7, x_8, x_9, x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_282; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_221);
x_282 = lean_infer_type(x_221, x_6, x_7, x_8, x_9, x_224);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_285 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_212, x_283, x_6, x_7, x_8, x_9, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_288 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_286, x_4, x_6, x_7, x_8, x_9, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_291 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_1, x_289, x_6, x_7, x_8, x_9, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_295 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_294, x_6, x_7, x_8, x_9, x_293);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_225 = x_296;
x_226 = x_297;
goto block_281;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_291, 1);
lean_inc(x_298);
lean_dec(x_291);
x_299 = lean_ctor_get(x_292, 0);
lean_inc(x_299);
lean_dec(x_292);
x_300 = lean_box(0);
x_301 = 1;
lean_inc(x_5);
x_302 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_302, 0, x_5);
lean_ctor_set(x_302, 1, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*2, x_301);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_303 = l_Lean_Meta_Simp_mkCongr(x_302, x_299, x_6, x_7, x_8, x_9, x_298);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_303, 0);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_307 = l_Lean_Meta_Simp_mkCongrFun(x_305, x_3, x_6, x_7, x_8, x_9, x_306);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_307, 0);
x_310 = lean_box(0);
lean_ctor_set(x_303, 1, x_310);
lean_ctor_set(x_303, 0, x_309);
lean_ctor_set(x_307, 0, x_303);
x_11 = x_307;
goto block_23;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_307, 0);
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_307);
x_313 = lean_box(0);
lean_ctor_set(x_303, 1, x_313);
lean_ctor_set(x_303, 0, x_311);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_312);
x_11 = x_314;
goto block_23;
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_free_object(x_303);
x_315 = lean_ctor_get(x_307, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_307, 1);
lean_inc(x_316);
lean_dec(x_307);
x_225 = x_315;
x_226 = x_316;
goto block_281;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_303, 0);
x_318 = lean_ctor_get(x_303, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_303);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_319 = l_Lean_Meta_Simp_mkCongrFun(x_317, x_3, x_6, x_7, x_8, x_9, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
x_323 = lean_box(0);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_323);
if (lean_is_scalar(x_322)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_322;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_321);
x_11 = x_325;
goto block_23;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_319, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_319, 1);
lean_inc(x_327);
lean_dec(x_319);
x_225 = x_326;
x_226 = x_327;
goto block_281;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_303, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_303, 1);
lean_inc(x_329);
lean_dec(x_303);
x_225 = x_328;
x_226 = x_329;
goto block_281;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_291, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_291, 1);
lean_inc(x_331);
lean_dec(x_291);
x_225 = x_330;
x_226 = x_331;
goto block_281;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_288, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 1);
lean_inc(x_333);
lean_dec(x_288);
x_225 = x_332;
x_226 = x_333;
goto block_281;
}
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_285, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_285, 1);
lean_inc(x_335);
lean_dec(x_285);
x_225 = x_334;
x_226 = x_335;
goto block_281;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_212);
x_336 = lean_ctor_get(x_282, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_282, 1);
lean_inc(x_337);
lean_dec(x_282);
x_139 = x_336;
x_140 = x_337;
goto block_203;
}
block_281:
{
uint8_t x_227; 
x_227 = l_Lean_Exception_isInterrupt(x_225);
if (x_227 == 0)
{
uint8_t x_228; 
x_228 = l_Lean_Exception_isRuntime(x_225);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_225);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_229 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_221, x_223, x_6, x_7, x_8, x_9, x_226);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_232 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_230, x_4, x_6, x_7, x_8, x_9, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_235 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_3, x_233, x_6, x_7, x_8, x_9, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_239 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_238, x_6, x_7, x_8, x_9, x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_139 = x_240;
x_140 = x_241;
goto block_203;
}
else
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_235);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_235, 1);
x_244 = lean_ctor_get(x_235, 0);
lean_dec(x_244);
x_245 = lean_ctor_get(x_236, 0);
lean_inc(x_245);
lean_dec(x_236);
lean_inc(x_1);
lean_inc(x_5);
x_246 = l_Lean_Expr_app___override(x_5, x_1);
x_247 = lean_box(0);
x_248 = 1;
x_249 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*2, x_248);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_250 = l_Lean_Meta_Simp_mkCongr(x_249, x_245, x_6, x_7, x_8, x_9, x_243);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_box(0);
lean_ctor_set(x_235, 1, x_253);
lean_ctor_set(x_235, 0, x_252);
lean_ctor_set(x_250, 0, x_235);
x_11 = x_250;
goto block_23;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_250, 0);
x_255 = lean_ctor_get(x_250, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_250);
x_256 = lean_box(0);
lean_ctor_set(x_235, 1, x_256);
lean_ctor_set(x_235, 0, x_254);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_235);
lean_ctor_set(x_257, 1, x_255);
x_11 = x_257;
goto block_23;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_free_object(x_235);
x_258 = lean_ctor_get(x_250, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_250, 1);
lean_inc(x_259);
lean_dec(x_250);
x_139 = x_258;
x_140 = x_259;
goto block_203;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_235, 1);
lean_inc(x_260);
lean_dec(x_235);
x_261 = lean_ctor_get(x_236, 0);
lean_inc(x_261);
lean_dec(x_236);
lean_inc(x_1);
lean_inc(x_5);
x_262 = l_Lean_Expr_app___override(x_5, x_1);
x_263 = lean_box(0);
x_264 = 1;
x_265 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set_uint8(x_265, sizeof(void*)*2, x_264);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_266 = l_Lean_Meta_Simp_mkCongr(x_265, x_261, x_6, x_7, x_8, x_9, x_260);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set(x_271, 1, x_270);
if (lean_is_scalar(x_269)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_269;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_268);
x_11 = x_272;
goto block_23;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_266, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
lean_dec(x_266);
x_139 = x_273;
x_140 = x_274;
goto block_203;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_235, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_235, 1);
lean_inc(x_276);
lean_dec(x_235);
x_139 = x_275;
x_140 = x_276;
goto block_203;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_232, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_232, 1);
lean_inc(x_278);
lean_dec(x_232);
x_139 = x_277;
x_140 = x_278;
goto block_203;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_229, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_229, 1);
lean_inc(x_280);
lean_dec(x_229);
x_139 = x_279;
x_140 = x_280;
goto block_203;
}
}
else
{
lean_dec(x_223);
lean_dec(x_221);
x_139 = x_225;
x_140 = x_226;
goto block_203;
}
}
else
{
lean_dec(x_223);
lean_dec(x_221);
x_139 = x_225;
x_140 = x_226;
goto block_203;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_221);
lean_dec(x_212);
x_338 = lean_ctor_get(x_222, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_222, 1);
lean_inc(x_339);
lean_dec(x_222);
x_139 = x_338;
x_140 = x_339;
goto block_203;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_212);
x_340 = lean_ctor_get(x_213, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_213, 1);
lean_inc(x_341);
lean_dec(x_213);
x_139 = x_340;
x_140 = x_341;
goto block_203;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_204, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_204, 1);
lean_inc(x_343);
lean_dec(x_204);
x_139 = x_342;
x_140 = x_343;
goto block_203;
}
block_23:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
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
block_42:
{
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
x_11 = x_29;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
x_11 = x_33;
goto block_23;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 1);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_24, 1, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
x_11 = x_37;
goto block_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
x_11 = x_41;
goto block_23;
}
}
}
block_57:
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_43, 1, x_47);
x_24 = x_43;
x_25 = x_44;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_24 = x_50;
x_25 = x_44;
goto block_42;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_43, 1);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_43, 1, x_53);
x_24 = x_43;
x_25 = x_44;
goto block_42;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_24 = x_56;
x_25 = x_44;
goto block_42;
}
}
}
block_69:
{
uint8_t x_60; 
x_60 = l_Lean_Exception_isInterrupt(x_58);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Exception_isRuntime(x_58);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_43 = x_66;
x_44 = x_59;
goto block_57;
}
else
{
lean_object* x_67; 
lean_dec(x_2);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
x_11 = x_67;
goto block_23;
}
}
else
{
lean_object* x_68; 
lean_dec(x_2);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
x_11 = x_68;
goto block_23;
}
}
block_138:
{
uint8_t x_72; 
x_72 = l_Lean_Exception_isInterrupt(x_70);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Exception_isRuntime(x_70);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_70);
lean_inc(x_1);
x_74 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_1);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_76 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_75, x_6, x_7, x_8, x_9, x_71);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_58 = x_77;
x_59 = x_78;
goto block_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_3, x_6, x_7, x_8, x_9, x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_85 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_84, x_6, x_7, x_8, x_9, x_83);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_58 = x_86;
x_59 = x_87;
goto block_69;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
lean_dec(x_82);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_90 = lean_infer_type(x_89, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l_Lean_Meta_mkNumeral(x_91, x_80, x_6, x_7, x_8, x_9, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_96 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_94, x_4, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_1, x_97, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_5);
lean_dec(x_3);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_103 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_102, x_6, x_7, x_8, x_9, x_101);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_58 = x_104;
x_59 = x_105;
goto block_69;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
lean_dec(x_100);
x_108 = lean_box(0);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_110, 0, x_5);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_109);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_111 = l_Lean_Meta_Simp_mkCongr(x_110, x_107, x_6, x_7, x_8, x_9, x_106);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Meta_Simp_mkCongrFun(x_112, x_3, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 1);
x_117 = lean_box(0);
lean_ctor_set(x_114, 1, x_117);
x_43 = x_114;
x_44 = x_116;
goto block_57;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_43 = x_121;
x_44 = x_119;
goto block_57;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_dec(x_114);
x_58 = x_122;
x_59 = x_123;
goto block_69;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_124 = lean_ctor_get(x_111, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_111, 1);
lean_inc(x_125);
lean_dec(x_111);
x_58 = x_124;
x_59 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_126 = lean_ctor_get(x_99, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_99, 1);
lean_inc(x_127);
lean_dec(x_99);
x_58 = x_126;
x_59 = x_127;
goto block_69;
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_128 = lean_ctor_get(x_96, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_96, 1);
lean_inc(x_129);
lean_dec(x_96);
x_58 = x_128;
x_59 = x_129;
goto block_69;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_130 = lean_ctor_get(x_93, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_93, 1);
lean_inc(x_131);
lean_dec(x_93);
x_58 = x_130;
x_59 = x_131;
goto block_69;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_90, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_90, 1);
lean_inc(x_133);
lean_dec(x_90);
x_58 = x_132;
x_59 = x_133;
goto block_69;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_134 = lean_ctor_get(x_81, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_81, 1);
lean_inc(x_135);
lean_dec(x_81);
x_58 = x_134;
x_59 = x_135;
goto block_69;
}
}
}
else
{
lean_object* x_136; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_70);
lean_ctor_set(x_136, 1, x_71);
x_11 = x_136;
goto block_23;
}
}
else
{
lean_object* x_137; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_70);
lean_ctor_set(x_137, 1, x_71);
x_11 = x_137;
goto block_23;
}
}
block_203:
{
uint8_t x_141; 
x_141 = l_Lean_Exception_isInterrupt(x_139);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Exception_isRuntime(x_139);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_139);
lean_inc(x_3);
x_143 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_3);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_145 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_144, x_6, x_7, x_8, x_9, x_140);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_70 = x_146;
x_71 = x_147;
goto block_138;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_150 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_1, x_6, x_7, x_8, x_9, x_140);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_154 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_153, x_6, x_7, x_8, x_9, x_152);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_70 = x_155;
x_71 = x_156;
goto block_138;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
lean_dec(x_151);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_159 = lean_infer_type(x_158, x_6, x_7, x_8, x_9, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_162 = l_Lean_Meta_mkNumeral(x_160, x_149, x_6, x_7, x_8, x_9, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_165 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_163, x_4, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_168 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_3, x_166, x_6, x_7, x_8, x_9, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_172 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_171, x_6, x_7, x_8, x_9, x_170);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_70 = x_173;
x_71 = x_174;
goto block_138;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
lean_dec(x_168);
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
lean_dec(x_169);
lean_inc(x_1);
lean_inc(x_5);
x_177 = l_Lean_Expr_app___override(x_5, x_1);
x_178 = lean_box(0);
x_179 = 1;
x_180 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*2, x_179);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_181 = l_Lean_Meta_Simp_mkCongr(x_180, x_176, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_181, 1);
x_184 = lean_box(0);
lean_ctor_set(x_181, 1, x_184);
x_24 = x_181;
x_25 = x_183;
goto block_42;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_181, 0);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_181);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_24 = x_188;
x_25 = x_186;
goto block_42;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_181, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_181, 1);
lean_inc(x_190);
lean_dec(x_181);
x_70 = x_189;
x_71 = x_190;
goto block_138;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_168, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_168, 1);
lean_inc(x_192);
lean_dec(x_168);
x_70 = x_191;
x_71 = x_192;
goto block_138;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_165, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_165, 1);
lean_inc(x_194);
lean_dec(x_165);
x_70 = x_193;
x_71 = x_194;
goto block_138;
}
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_162, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_162, 1);
lean_inc(x_196);
lean_dec(x_162);
x_70 = x_195;
x_71 = x_196;
goto block_138;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_149);
x_197 = lean_ctor_get(x_159, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_159, 1);
lean_inc(x_198);
lean_dec(x_159);
x_70 = x_197;
x_71 = x_198;
goto block_138;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_149);
x_199 = lean_ctor_get(x_150, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_150, 1);
lean_inc(x_200);
lean_dec(x_150);
x_70 = x_199;
x_71 = x_200;
goto block_138;
}
}
}
else
{
lean_object* x_201; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_139);
lean_ctor_set(x_201, 1, x_140);
x_11 = x_201;
goto block_23;
}
}
else
{
lean_object* x_202; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_139);
lean_ctor_set(x_202, 1, x_140);
x_11 = x_202;
goto block_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("splitting ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_1);
x_12 = l_Lean_MessageData_ofExpr(x_1);
x_13 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___boxed), 9, 3);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__2), 10, 5);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
x_19 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
x_20 = 1;
x_21 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
x_22 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_19, x_17, x_18, x_20, x_21, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3(x_3, x_4, x_5, x_1, x_6, x_27, x_8, x_9, x_10, x_11, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_11 = lean_infer_type(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 7)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Expr_hasLooseBVars(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasLooseBVars(x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4(x_17, x_18, x_1, x_10, x_8, x_9, x_22, x_2, x_3, x_4, x_5, x_15);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_25);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 2);
lean_inc(x_33);
lean_dec(x_13);
x_34 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasLooseBVars(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4(x_31, x_32, x_1, x_10, x_8, x_9, x_36, x_2, x_3, x_4, x_5, x_30);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_11, 0);
lean_dec(x_47);
x_48 = lean_box(0);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_49);
lean_ctor_set(x_11, 0, x_50);
return x_11;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_dec(x_11);
x_52 = lean_box(0);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_11, 0);
lean_dec(x_57);
x_58 = lean_box(0);
x_59 = 1;
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_59);
lean_ctor_set(x_11, 0, x_60);
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
x_62 = lean_box(0);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_11);
if (x_66 == 0)
{
return x_11;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = 1;
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_6);
return x_73;
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = 1;
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox_float(x_9);
lean_dec(x_9);
x_20 = lean_unbox_float(x_10);
lean_dec(x_10);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; double x_19; double x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox_float(x_8);
lean_dec(x_8);
x_20 = lean_unbox_float(x_9);
lean_dec(x_9);
x_21 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__3(x_1, x_17, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___lambda__4(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_12);
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_discharge_x3f_x27___spec__8(x_1, x_5, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
lean_dec(x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, double x_9, double x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
double x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set_float(x_21, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_21, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 16, x_2);
x_22 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2;
x_23 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_22);
if (x_23 == 0)
{
if (x_8 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_21, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_2);
x_27 = lean_box(0);
x_28 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_26, x_27, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set_float(x_29, sizeof(void*)*2, x_9);
lean_ctor_set_float(x_29, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 16, x_2);
x_30 = lean_box(0);
x_31 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(x_4, x_5, x_11, x_6, x_29, x_30, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 5);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_21 = lean_apply_9(x_10, x_5, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_20, x_5, x_6, x_7, x_8, x_9, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2;
x_27 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_20, x_5, x_6, x_7, x_8, x_9, x_26, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_25);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_discharge_x3f_x27___spec__7___rarg(x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1;
x_21 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_io_mono_nanos_now(x_19);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_99 = lean_apply_8(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_io_mono_nanos_now(x_102);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; double x_110; double x_111; double x_112; double x_113; double x_114; lean_object* x_115; lean_object* x_116; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
x_108 = 0;
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Float_ofScientific(x_97, x_108, x_109);
lean_dec(x_97);
x_111 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_112 = lean_float_div(x_110, x_111);
x_113 = l_Float_ofScientific(x_106, x_108, x_109);
lean_dec(x_106);
x_114 = lean_float_div(x_113, x_111);
x_115 = lean_box_float(x_112);
x_116 = lean_box_float(x_114);
lean_ctor_set(x_104, 1, x_116);
lean_ctor_set(x_104, 0, x_115);
lean_ctor_set(x_99, 1, x_104);
lean_ctor_set(x_99, 0, x_103);
x_22 = x_99;
x_23 = x_107;
goto block_95;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; double x_121; double x_122; double x_123; double x_124; double x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_117 = lean_ctor_get(x_104, 0);
x_118 = lean_ctor_get(x_104, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_104);
x_119 = 0;
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Float_ofScientific(x_97, x_119, x_120);
lean_dec(x_97);
x_122 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_123 = lean_float_div(x_121, x_122);
x_124 = l_Float_ofScientific(x_117, x_119, x_120);
lean_dec(x_117);
x_125 = lean_float_div(x_124, x_122);
x_126 = lean_box_float(x_123);
x_127 = lean_box_float(x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_99, 1, x_128);
lean_ctor_set(x_99, 0, x_103);
x_22 = x_99;
x_23 = x_118;
goto block_95;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; double x_138; double x_139; double x_140; double x_141; double x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_129 = lean_ctor_get(x_99, 0);
x_130 = lean_ctor_get(x_99, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_99);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_129);
x_132 = lean_io_mono_nanos_now(x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = 0;
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Float_ofScientific(x_97, x_136, x_137);
lean_dec(x_97);
x_139 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_140 = lean_float_div(x_138, x_139);
x_141 = l_Float_ofScientific(x_133, x_136, x_137);
lean_dec(x_133);
x_142 = lean_float_div(x_141, x_139);
x_143 = lean_box_float(x_140);
x_144 = lean_box_float(x_142);
if (lean_is_scalar(x_135)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_135;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_131);
lean_ctor_set(x_146, 1, x_145);
x_22 = x_146;
x_23 = x_134;
goto block_95;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_99);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_99, 0);
x_149 = lean_ctor_get(x_99, 1);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_148);
x_151 = lean_io_mono_nanos_now(x_149);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; double x_157; double x_158; double x_159; double x_160; double x_161; lean_object* x_162; lean_object* x_163; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = 0;
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Float_ofScientific(x_97, x_155, x_156);
lean_dec(x_97);
x_158 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_159 = lean_float_div(x_157, x_158);
x_160 = l_Float_ofScientific(x_153, x_155, x_156);
lean_dec(x_153);
x_161 = lean_float_div(x_160, x_158);
x_162 = lean_box_float(x_159);
x_163 = lean_box_float(x_161);
lean_ctor_set(x_151, 1, x_163);
lean_ctor_set(x_151, 0, x_162);
lean_ctor_set_tag(x_99, 0);
lean_ctor_set(x_99, 1, x_151);
lean_ctor_set(x_99, 0, x_150);
x_22 = x_99;
x_23 = x_154;
goto block_95;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; double x_168; double x_169; double x_170; double x_171; double x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_164 = lean_ctor_get(x_151, 0);
x_165 = lean_ctor_get(x_151, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_151);
x_166 = 0;
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Float_ofScientific(x_97, x_166, x_167);
lean_dec(x_97);
x_169 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_170 = lean_float_div(x_168, x_169);
x_171 = l_Float_ofScientific(x_164, x_166, x_167);
lean_dec(x_164);
x_172 = lean_float_div(x_171, x_169);
x_173 = lean_box_float(x_170);
x_174 = lean_box_float(x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set_tag(x_99, 0);
lean_ctor_set(x_99, 1, x_175);
lean_ctor_set(x_99, 0, x_150);
x_22 = x_99;
x_23 = x_165;
goto block_95;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; double x_185; double x_186; double x_187; double x_188; double x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_176 = lean_ctor_get(x_99, 0);
x_177 = lean_ctor_get(x_99, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_99);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_176);
x_179 = lean_io_mono_nanos_now(x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = 0;
x_184 = lean_unsigned_to_nat(0u);
x_185 = l_Float_ofScientific(x_97, x_183, x_184);
lean_dec(x_97);
x_186 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5;
x_187 = lean_float_div(x_185, x_186);
x_188 = l_Float_ofScientific(x_180, x_183, x_184);
lean_dec(x_180);
x_189 = lean_float_div(x_188, x_186);
x_190 = lean_box_float(x_187);
x_191 = lean_box_float(x_189);
if (lean_is_scalar(x_182)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_182;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_178);
lean_ctor_set(x_193, 1, x_192);
x_22 = x_193;
x_23 = x_181;
goto block_95;
}
}
block_95:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_75; uint8_t x_76; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_75 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_76 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
x_28 = x_77;
goto block_74;
}
else
{
double x_78; double x_79; double x_80; 
x_78 = lean_unbox_float(x_27);
x_79 = lean_unbox_float(x_26);
x_80 = lean_float_sub(x_78, x_79);
if (x_21 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; double x_85; double x_86; double x_87; uint8_t x_88; 
x_81 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_82 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_81);
x_83 = 0;
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Float_ofScientific(x_82, x_83, x_84);
lean_dec(x_82);
x_86 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4;
x_87 = lean_float_div(x_85, x_86);
x_88 = lean_float_decLt(x_87, x_80);
x_28 = x_88;
goto block_74;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; double x_93; uint8_t x_94; 
x_89 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_90 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_89);
x_91 = 0;
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Float_ofScientific(x_90, x_91, x_92);
lean_dec(x_90);
x_94 = lean_float_decLt(x_93, x_80);
x_28 = x_94;
goto block_74;
}
}
block_74:
{
if (x_6 == 0)
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_st_ref_take(x_15, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_30, 3);
x_34 = l_Lean_PersistentArray_append___rarg(x_18, x_33);
lean_dec(x_33);
lean_ctor_set(x_30, 3, x_34);
x_35 = lean_st_ref_set(x_15, x_30, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_25);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
x_48 = lean_ctor_get(x_30, 2);
x_49 = lean_ctor_get(x_30, 3);
x_50 = lean_ctor_get(x_30, 4);
x_51 = lean_ctor_get(x_30, 5);
x_52 = lean_ctor_get(x_30, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_53 = l_Lean_PersistentArray_append___rarg(x_18, x_49);
lean_dec(x_49);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set(x_54, 6, x_52);
x_55 = lean_st_ref_set(x_15, x_54, x_31);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_25);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; double x_67; double x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_unbox_float(x_26);
lean_dec(x_26);
x_68 = lean_unbox_float(x_27);
lean_dec(x_27);
x_69 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(x_2, x_3, x_4, x_18, x_25, x_1, x_28, x_67, x_68, x_5, x_66, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
return x_69;
}
}
else
{
lean_object* x_70; double x_71; double x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = lean_unbox_float(x_26);
lean_dec(x_26);
x_72 = lean_unbox_float(x_27);
lean_dec(x_27);
x_73 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(x_2, x_3, x_4, x_18, x_25, x_1, x_28, x_71, x_72, x_5, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
return x_73;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_io_get_num_heartbeats(x_19);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_271 = lean_apply_8(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_270);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_271, 0);
x_274 = lean_ctor_get(x_271, 1);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_273);
x_276 = lean_io_get_num_heartbeats(x_274);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; double x_282; double x_283; lean_object* x_284; lean_object* x_285; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
x_280 = 0;
x_281 = lean_unsigned_to_nat(0u);
x_282 = l_Float_ofScientific(x_269, x_280, x_281);
lean_dec(x_269);
x_283 = l_Float_ofScientific(x_278, x_280, x_281);
lean_dec(x_278);
x_284 = lean_box_float(x_282);
x_285 = lean_box_float(x_283);
lean_ctor_set(x_276, 1, x_285);
lean_ctor_set(x_276, 0, x_284);
lean_ctor_set(x_271, 1, x_276);
lean_ctor_set(x_271, 0, x_275);
x_194 = x_271;
x_195 = x_279;
goto block_267;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; double x_290; double x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_286 = lean_ctor_get(x_276, 0);
x_287 = lean_ctor_get(x_276, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_276);
x_288 = 0;
x_289 = lean_unsigned_to_nat(0u);
x_290 = l_Float_ofScientific(x_269, x_288, x_289);
lean_dec(x_269);
x_291 = l_Float_ofScientific(x_286, x_288, x_289);
lean_dec(x_286);
x_292 = lean_box_float(x_290);
x_293 = lean_box_float(x_291);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_271, 1, x_294);
lean_ctor_set(x_271, 0, x_275);
x_194 = x_271;
x_195 = x_287;
goto block_267;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; double x_304; double x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_295 = lean_ctor_get(x_271, 0);
x_296 = lean_ctor_get(x_271, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_271);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_295);
x_298 = lean_io_get_num_heartbeats(x_296);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = 0;
x_303 = lean_unsigned_to_nat(0u);
x_304 = l_Float_ofScientific(x_269, x_302, x_303);
lean_dec(x_269);
x_305 = l_Float_ofScientific(x_299, x_302, x_303);
lean_dec(x_299);
x_306 = lean_box_float(x_304);
x_307 = lean_box_float(x_305);
if (lean_is_scalar(x_301)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_301;
}
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_297);
lean_ctor_set(x_309, 1, x_308);
x_194 = x_309;
x_195 = x_300;
goto block_267;
}
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_271);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_271, 0);
x_312 = lean_ctor_get(x_271, 1);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_311);
x_314 = lean_io_get_num_heartbeats(x_312);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; double x_320; double x_321; lean_object* x_322; lean_object* x_323; 
x_316 = lean_ctor_get(x_314, 0);
x_317 = lean_ctor_get(x_314, 1);
x_318 = 0;
x_319 = lean_unsigned_to_nat(0u);
x_320 = l_Float_ofScientific(x_269, x_318, x_319);
lean_dec(x_269);
x_321 = l_Float_ofScientific(x_316, x_318, x_319);
lean_dec(x_316);
x_322 = lean_box_float(x_320);
x_323 = lean_box_float(x_321);
lean_ctor_set(x_314, 1, x_323);
lean_ctor_set(x_314, 0, x_322);
lean_ctor_set_tag(x_271, 0);
lean_ctor_set(x_271, 1, x_314);
lean_ctor_set(x_271, 0, x_313);
x_194 = x_271;
x_195 = x_317;
goto block_267;
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; double x_328; double x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_324 = lean_ctor_get(x_314, 0);
x_325 = lean_ctor_get(x_314, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_314);
x_326 = 0;
x_327 = lean_unsigned_to_nat(0u);
x_328 = l_Float_ofScientific(x_269, x_326, x_327);
lean_dec(x_269);
x_329 = l_Float_ofScientific(x_324, x_326, x_327);
lean_dec(x_324);
x_330 = lean_box_float(x_328);
x_331 = lean_box_float(x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set_tag(x_271, 0);
lean_ctor_set(x_271, 1, x_332);
lean_ctor_set(x_271, 0, x_313);
x_194 = x_271;
x_195 = x_325;
goto block_267;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; double x_342; double x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_333 = lean_ctor_get(x_271, 0);
x_334 = lean_ctor_get(x_271, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_271);
x_335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_335, 0, x_333);
x_336 = lean_io_get_num_heartbeats(x_334);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
x_340 = 0;
x_341 = lean_unsigned_to_nat(0u);
x_342 = l_Float_ofScientific(x_269, x_340, x_341);
lean_dec(x_269);
x_343 = l_Float_ofScientific(x_337, x_340, x_341);
lean_dec(x_337);
x_344 = lean_box_float(x_342);
x_345 = lean_box_float(x_343);
if (lean_is_scalar(x_339)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_339;
}
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_335);
lean_ctor_set(x_347, 1, x_346);
x_194 = x_347;
x_195 = x_338;
goto block_267;
}
}
block_267:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_247; uint8_t x_248; 
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_247 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_248 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_247);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = 0;
x_200 = x_249;
goto block_246;
}
else
{
double x_250; double x_251; double x_252; 
x_250 = lean_unbox_float(x_199);
x_251 = lean_unbox_float(x_198);
x_252 = lean_float_sub(x_250, x_251);
if (x_21 == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; double x_257; double x_258; double x_259; uint8_t x_260; 
x_253 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_254 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_253);
x_255 = 0;
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Float_ofScientific(x_254, x_255, x_256);
lean_dec(x_254);
x_258 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4;
x_259 = lean_float_div(x_257, x_258);
x_260 = lean_float_decLt(x_259, x_252);
x_200 = x_260;
goto block_246;
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; double x_265; uint8_t x_266; 
x_261 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3;
x_262 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_261);
x_263 = 0;
x_264 = lean_unsigned_to_nat(0u);
x_265 = l_Float_ofScientific(x_262, x_263, x_264);
lean_dec(x_262);
x_266 = lean_float_decLt(x_265, x_252);
x_200 = x_266;
goto block_246;
}
}
block_246:
{
if (x_6 == 0)
{
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_201 = lean_st_ref_take(x_15, x_195);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = !lean_is_exclusive(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_202, 3);
x_206 = l_Lean_PersistentArray_append___rarg(x_18, x_205);
lean_dec(x_205);
lean_ctor_set(x_202, 3, x_206);
x_207 = lean_st_ref_set(x_15, x_202, x_203);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_197, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_208);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_197);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_209);
if (x_214 == 0)
{
return x_209;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_209, 0);
x_216 = lean_ctor_get(x_209, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_209);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_218 = lean_ctor_get(x_202, 0);
x_219 = lean_ctor_get(x_202, 1);
x_220 = lean_ctor_get(x_202, 2);
x_221 = lean_ctor_get(x_202, 3);
x_222 = lean_ctor_get(x_202, 4);
x_223 = lean_ctor_get(x_202, 5);
x_224 = lean_ctor_get(x_202, 6);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_202);
x_225 = l_Lean_PersistentArray_append___rarg(x_18, x_221);
lean_dec(x_221);
x_226 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_219);
lean_ctor_set(x_226, 2, x_220);
lean_ctor_set(x_226, 3, x_225);
lean_ctor_set(x_226, 4, x_222);
lean_ctor_set(x_226, 5, x_223);
lean_ctor_set(x_226, 6, x_224);
x_227 = lean_st_ref_set(x_15, x_226, x_203);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_197, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_228);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_197);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_229, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_236 = x_229;
} else {
 lean_dec_ref(x_229);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_238; double x_239; double x_240; lean_object* x_241; 
x_238 = lean_box(0);
x_239 = lean_unbox_float(x_198);
lean_dec(x_198);
x_240 = lean_unbox_float(x_199);
lean_dec(x_199);
x_241 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(x_2, x_3, x_4, x_18, x_197, x_1, x_200, x_239, x_240, x_5, x_238, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_195);
return x_241;
}
}
else
{
lean_object* x_242; double x_243; double x_244; lean_object* x_245; 
x_242 = lean_box(0);
x_243 = lean_unbox_float(x_198);
lean_dec(x_198);
x_244 = lean_unbox_float(x_199);
lean_dec(x_199);
x_245 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(x_2, x_3, x_4, x_18, x_197, x_1, x_200, x_243, x_244, x_5, x_242, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_195);
return x_245;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_inc(x_1);
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_apply_8(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_16);
lean_dec(x_16);
x_32 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4(x_14, x_1, x_4, x_5, x_2, x_31, x_3, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
lean_dec(x_14);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = lean_unbox(x_16);
lean_dec(x_16);
x_36 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4(x_14, x_1, x_4, x_5, x_2, x_35, x_3, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_14);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" discharging: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = l_Lean_exceptOptionEmoji___rarg(x_2);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_findLocalDeclWithType_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Expr_fvar___override(x_13);
lean_ctor_set(x_1, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Expr_fvar___override(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lambda__3___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lambda__1___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lambda__2___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_NormCast_prove___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_discharge_x3f_x27___spec__5___rarg), 10, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
x_15 = 1;
x_16 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
x_17 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1(x_14, x_10, x_13, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_MonadExcept_ofExcept___at_Lean_Elab_Tactic_NormCast_prove___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; double x_22; double x_23; lean_object* x_24; 
x_20 = lean_unbox(x_2);
lean_dec(x_2);
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = lean_unbox_float(x_9);
lean_dec(x_9);
x_23 = lean_unbox_float(x_10);
lean_dec(x_10);
x_24 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__2(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_21, x_22, x_23, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; double x_22; double x_23; lean_object* x_24; 
x_20 = lean_unbox(x_2);
lean_dec(x_2);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = lean_unbox_float(x_8);
lean_dec(x_8);
x_23 = lean_unbox_float(x_9);
lean_dec(x_9);
x_24 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__3(x_1, x_20, x_3, x_4, x_5, x_6, x_21, x_22, x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_11);
lean_dec(x_6);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___lambda__4(x_1, x_2, x_17, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_prove___spec__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_prove___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_prove___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_prove___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("squash", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_114 = lean_st_ref_get(x_5, x_10);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_take(x_5, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
x_123 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7;
lean_ctor_set(x_119, 0, x_123);
x_124 = lean_st_ref_set(x_5, x_119, x_120);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_3, 0);
x_127 = lean_ctor_get(x_3, 1);
x_128 = lean_ctor_get(x_3, 2);
x_129 = lean_ctor_get(x_3, 3);
x_130 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1;
x_131 = 0;
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
x_132 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_128);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*5, x_131);
x_133 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_134 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_11, x_12, x_133, x_131, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_st_ref_take(x_5, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_138, 0);
lean_dec(x_141);
lean_ctor_set(x_138, 0, x_117);
x_142 = lean_st_ref_set(x_5, x_138, x_139);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
lean_ctor_set(x_142, 0, x_135);
x_13 = x_142;
goto block_113;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_145);
x_13 = x_146;
goto block_113;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_138, 1);
x_148 = lean_ctor_get(x_138, 2);
x_149 = lean_ctor_get(x_138, 3);
x_150 = lean_ctor_get(x_138, 4);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_138);
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_117);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_151, 2, x_148);
lean_ctor_set(x_151, 3, x_149);
lean_ctor_set(x_151, 4, x_150);
x_152 = lean_st_ref_set(x_5, x_151, x_139);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_135);
lean_ctor_set(x_155, 1, x_153);
x_13 = x_155;
goto block_113;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_134, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_134, 1);
lean_inc(x_157);
lean_dec(x_134);
x_158 = lean_st_ref_take(x_5, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_159, 0);
lean_dec(x_162);
lean_ctor_set(x_159, 0, x_117);
x_163 = lean_st_ref_set(x_5, x_159, x_160);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
lean_ctor_set_tag(x_163, 1);
lean_ctor_set(x_163, 0, x_156);
x_13 = x_163;
goto block_113;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_166);
x_13 = x_167;
goto block_113;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_159, 1);
x_169 = lean_ctor_get(x_159, 2);
x_170 = lean_ctor_get(x_159, 3);
x_171 = lean_ctor_get(x_159, 4);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_159);
x_172 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_172, 0, x_117);
lean_ctor_set(x_172, 1, x_168);
lean_ctor_set(x_172, 2, x_169);
lean_ctor_set(x_172, 3, x_170);
lean_ctor_set(x_172, 4, x_171);
x_173 = lean_st_ref_set(x_5, x_172, x_160);
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
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_156);
lean_ctor_set(x_176, 1, x_174);
x_13 = x_176;
goto block_113;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_177 = lean_ctor_get(x_119, 1);
x_178 = lean_ctor_get(x_119, 2);
x_179 = lean_ctor_get(x_119, 3);
x_180 = lean_ctor_get(x_119, 4);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_119);
x_181 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7;
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_177);
lean_ctor_set(x_182, 2, x_178);
lean_ctor_set(x_182, 3, x_179);
lean_ctor_set(x_182, 4, x_180);
x_183 = lean_st_ref_set(x_5, x_182, x_120);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_3, 0);
x_186 = lean_ctor_get(x_3, 1);
x_187 = lean_ctor_get(x_3, 2);
x_188 = lean_ctor_get(x_3, 3);
x_189 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1;
x_190 = 0;
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_191 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_186);
lean_ctor_set(x_191, 2, x_187);
lean_ctor_set(x_191, 3, x_188);
lean_ctor_set(x_191, 4, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*5, x_190);
x_192 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_193 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_11, x_12, x_192, x_190, x_191, x_4, x_5, x_6, x_7, x_8, x_9, x_184);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_st_ref_take(x_5, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 4);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_117);
lean_ctor_set(x_204, 1, x_199);
lean_ctor_set(x_204, 2, x_200);
lean_ctor_set(x_204, 3, x_201);
lean_ctor_set(x_204, 4, x_202);
x_205 = lean_st_ref_set(x_5, x_204, x_198);
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
lean_ctor_set(x_208, 0, x_194);
lean_ctor_set(x_208, 1, x_206);
x_13 = x_208;
goto block_113;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_209 = lean_ctor_get(x_193, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_193, 1);
lean_inc(x_210);
lean_dec(x_193);
x_211 = lean_st_ref_take(x_5, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 4);
lean_inc(x_217);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 x_218 = x_212;
} else {
 lean_dec_ref(x_212);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_117);
lean_ctor_set(x_219, 1, x_214);
lean_ctor_set(x_219, 2, x_215);
lean_ctor_set(x_219, 3, x_216);
lean_ctor_set(x_219, 4, x_217);
x_220 = lean_st_ref_set(x_5, x_219, x_213);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_222 = x_220;
} else {
 lean_dec_ref(x_220);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
 lean_ctor_set_tag(x_223, 1);
}
lean_ctor_set(x_223, 0, x_209);
lean_ctor_set(x_223, 1, x_221);
x_13 = x_223;
goto block_113;
}
}
block_113:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 1;
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_NormCast_splittingProcedure(x_2, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_18);
x_22 = l_Lean_Meta_Simp_Result_mkEqTrans(x_18, x_20, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_expr_eqv(x_26, x_2);
lean_dec(x_2);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_22);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_24, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_expr_eqv(x_33, x_2);
lean_dec(x_2);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_18);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_31, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_18);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Lean_Elab_Tactic_NormCast_splittingProcedure(x_50, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_54 = l_Lean_Meta_Simp_Result_mkEqTrans(x_49, x_52, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_expr_eqv(x_58, x_2);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_54);
lean_free_object(x_14);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_56, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_box(0);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_63);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_64);
lean_ctor_set(x_54, 0, x_14);
return x_54;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_expr_eqv(x_67, x_2);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_free_object(x_14);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_65, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_70;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_box(0);
x_72 = 1;
x_73 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_72);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_free_object(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_54);
if (x_75 == 0)
{
return x_54;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_54, 0);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_54);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_14);
lean_dec(x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_51);
if (x_79 == 0)
{
return x_51;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_51, 0);
x_81 = lean_ctor_get(x_51, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_51);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_14, 0);
lean_inc(x_83);
lean_dec(x_14);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_85 = l_Lean_Elab_Tactic_NormCast_splittingProcedure(x_84, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Meta_Simp_Result_mkEqTrans(x_83, x_86, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_expr_eqv(x_92, x_2);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_2);
x_94 = lean_box(0);
x_95 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_89, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_89);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = lean_box(0);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_90);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_103 = x_88;
} else {
 lean_dec_ref(x_88);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_83);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_105 = lean_ctor_get(x_85, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_85, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_107 = x_85;
} else {
 lean_dec_ref(x_85);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_13);
if (x_109 == 0)
{
return x_13;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_13, 0);
x_111 = lean_ctor_get(x_13, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_13);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_upwardAndElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1;
x_2 = l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = l_Lean_mkNatLit(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_mk(x_17);
x_19 = l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_mkAppOptM(x_19, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_3, x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_27 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_26, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
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
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_13 = lean_whnf(x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6;
x_17 = l_Lean_Expr_isConstOf(x_14, x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1(x_11, x_12, x_1, x_18, x_2, x_3, x_4, x_5, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_20 = l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2;
x_21 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_20, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_11);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_MessageData_ofExpr(x_1);
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_NormCast_numeralToCoe(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
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
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = l_Lean_Exception_isInterrupt(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__5___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l_Lean_Meta_Simp_mkContext(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__3___boxed), 10, 1);
lean_closure_set(x_16, 0, x_4);
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__4___boxed), 10, 1);
lean_closure_set(x_17, 0, x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__6___boxed), 10, 1);
lean_closure_set(x_18, 0, x_4);
x_19 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2;
x_20 = 1;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_20);
x_22 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_Simp_main(x_6, x_14, x_22, x_21, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Simp_Result_mkEqTrans(x_7, x_26, x_8, x_9, x_10, x_11, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_2 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1;
x_2 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pre-processing numerals", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2;
x_2 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (after ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_MessageData_ofExpr(x_10);
x_12 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = l_Lean_Meta_Simp_mkContext(x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_inc(x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__3___boxed), 10, 1);
lean_closure_set(x_20, 0, x_6);
lean_inc(x_6);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__4___boxed), 10, 1);
lean_closure_set(x_21, 0, x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__6___boxed), 10, 1);
lean_closure_set(x_22, 0, x_6);
x_23 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2;
x_24 = 1;
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_24);
x_26 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Meta_Simp_main(x_19, x_17, x_26, x_25, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Simp_Result_mkEqTrans(x_5, x_30, x_7, x_8, x_9, x_10, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moving upward, splitting and eliminating", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2;
x_2 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_MessageData_ofExpr(x_10);
x_12 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_15);
x_16 = lean_array_mk(x_12);
x_17 = l_Lean_Meta_Simp_mkContext(x_2, x_16, x_3, x_7, x_8, x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_simp(x_20, x_18, x_5, x_6, x_21, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Simp_Result_mkEqTrans(x_4, x_25, x_7, x_8, x_9, x_10, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_mk(x_34);
x_36 = l_Lean_Meta_Simp_mkContext(x_2, x_35, x_3, x_7, x_8, x_9, x_10, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Lean_Meta_simp(x_39, x_37, x_5, x_6, x_40, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_Simp_Result_mkEqTrans(x_4, x_44, x_7, x_8, x_9, x_10, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
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
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("squashing", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2;
x_2 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_MessageData_ofExpr(x_10);
x_12 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__10___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceCtorEq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__12___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = 1;
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__2___boxed), 10, 1);
lean_closure_set(x_17, 0, x_14);
x_18 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1;
x_19 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2;
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__7), 12, 7);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_12);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_17);
lean_closure_set(x_20, 5, x_9);
lean_closure_set(x_20, 6, x_16);
x_21 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3;
x_22 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_2, x_21, x_20, x_15, x_22, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_NormCast_normCastExt;
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_inc(x_12);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__9___boxed), 11, 6);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_18);
lean_closure_set(x_28, 2, x_19);
lean_closure_set(x_28, 3, x_12);
lean_closure_set(x_28, 4, x_24);
lean_closure_set(x_28, 5, x_14);
x_29 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_2, x_29, x_28, x_15, x_22, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6;
x_34 = 0;
x_35 = l_Lean_Meta_Simp_SimprocsArray_add(x_19, x_33, x_34, x_5, x_6, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_26, 2);
lean_inc(x_38);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__11___boxed), 11, 6);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_18);
lean_closure_set(x_39, 2, x_12);
lean_closure_set(x_39, 3, x_31);
lean_closure_set(x_39, 4, x_36);
lean_closure_set(x_39, 5, x_14);
x_40 = l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7;
x_41 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_2, x_40, x_39, x_15, x_22, x_3, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
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
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
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
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_23);
if (x_58 == 0)
{
return x_23;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_23, 0);
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_23);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__1___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lambda__13), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = 1;
x_11 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1;
x_12 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_splittingProcedure___spec__2(x_8, x_7, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_NormCast_derive___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_derive___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_derive___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_derive___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_derive___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_Simp_Result_mkEqSymm(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
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
x_16 = l_Lean_Meta_Simp_Result_mkEqTrans(x_3, x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Simp_Result_mkCast(x_17, x_4, x_8, x_9, x_10, x_11, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
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
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod_cast", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Elab_Tactic_NormCast_derive(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_17);
x_18 = l_Lean_Meta_isExprDefEq(x_17, x_2, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4;
x_24 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_23, x_2, x_17, x_5, x_22, x_22, x_9, x_10, x_11, x_12, x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_2);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1(x_3, x_4, x_15, x_5, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Elab_Tactic_NormCast_derive(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Elab_Term_elabTerm(x_2, x_15, x_16, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_18);
x_24 = lean_infer_type(x_18, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_hasExprMVar(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2(x_28, x_14, x_1, x_12, x_18, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Term_tryPostpone(x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2(x_28, x_14, x_1, x_12, x_18, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
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
uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
x_10 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_hasExprMVar(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3(x_2, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Term_tryPostpone(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_17);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("modCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__4), 9, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_withExpectedType(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabModCast", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3;
x_3 = l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(224u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(44u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_MVarId_getType(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_20 = l_Lean_Elab_Tactic_NormCast_derive(x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_applySimpResultToTarget(x_11, x_18, x_21, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_24);
x_27 = l_Lean_Elab_Tactic_replaceMainGoal(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
else
{
uint8_t x_28; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
uint8_t x_32; 
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l_Lean_Elab_Tactic_NormCast_derive(x_36, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_applySimpResultToTarget(x_11, x_36, x_39, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Tactic_replaceMainGoal(x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
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
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_10);
if (x_59 == 0)
{
return x_10;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_normCastTarget___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_20; 
x_20 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_FVarId_getDecl(x_1, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
x_27 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_26, x_6, x_7, x_8, x_9, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lean_Elab_Tactic_NormCast_derive(x_28, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_34 = l_Lean_Meta_applySimpResultToLocalDecl(x_21, x_1, x_31, x_33, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_11 = x_37;
x_12 = x_36;
goto block_19;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_ctor_set(x_35, 0, x_41);
x_11 = x_35;
x_12 = x_38;
goto block_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_11 = x_44;
x_12 = x_38;
goto block_19;
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
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
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
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
return x_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_19:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_replaceMainGoal(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_normCastHyp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Tactic_NormCast_normCastHyp(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_array_get_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(0);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_12);
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(x_14, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_14);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_array_get_size(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_28, x_28);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = lean_box(0);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(x_26, x_36, x_37, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_26);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_MVarId_getNondepPropHyps(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_get_size(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_16);
x_26 = 0;
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(x_18, x_26, x_27, x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_18);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_array_get_size(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_32, x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_42 = lean_box(0);
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(x_30, x_40, x_41, x_42, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_30);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
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
lean_dec(x_1);
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
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__3), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1;
x_22 = 1;
x_12 = x_21;
x_13 = x_22;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_Lean_Elab_Tactic_expandLocation(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2;
x_26 = l_Lean_Elab_Tactic_withMainContext___rarg(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_24, sizeof(void*)*1);
lean_dec(x_24);
x_12 = x_27;
x_13 = x_28;
goto block_20;
}
}
block_20:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1___boxed), 11, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_withMainContext___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1___boxed), 11, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__2), 10, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("normCast0", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___boxed), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4;
x_17 = l_Lean_Syntax_isNone(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_15);
x_18 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = lean_apply_11(x_16, x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_apply_11(x_16, x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_NormCast_evalNormCast0___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalNormCast0", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3;
x_3 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(241u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(253u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(241u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(241u);
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(17u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_13 = l_Lean_Elab_Tactic_NormCast_derive(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Conv", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("normCast", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalConvNormCast", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(258u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(20u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_expandOptLocation(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_NormCast_pushCastExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = 0;
x_12 = 0;
x_13 = l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2;
x_14 = lean_box(x_11);
x_15 = lean_box(x_12);
x_16 = lean_box(x_11);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_21, x_11);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1___boxed), 13, 3);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_22);
x_26 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_23, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_NormCast_evalPushCast___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pushCast", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalPushCast", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(261u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(266u);
x_2 = lean_unsigned_to_nat(78u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(78u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(261u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(261u);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(16u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_realizeGlobalConstNoOverload(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 0;
x_11 = lean_unsigned_to_nat(1000u);
x_12 = l_Lean_Meta_NormCast_addElim(x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("normCastAddElim", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 13);
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
lean_ctor_set_uint8(x_5, 12, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5;
x_3 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6;
x_4 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9;
x_2 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10;
x_4 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_3);
lean_ctor_set(x_4, 6, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8;
x_3 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11;
x_4 = l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11;
x_5 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lambda__1), 6, 1);
lean_closure_set(x_13, 0, x_9);
x_14 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7;
x_15 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13;
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg), 6, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_Elab_Command_liftCoreM___rarg(x_16, x_2, x_3, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_NormCast_elabAddElim(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabAddElim", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4;
x_2 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6;
x_3 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1;
x_4 = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3;
x_3 = l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(269u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(274u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(269u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(269u);
x_2 = lean_unsigned_to_nat(69u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(58u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(69u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_NormCast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__1);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__2);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__3);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__4);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__5);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__6);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__7);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__8);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__9);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__10);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__11);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__12);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__13);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__14);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__15);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__16);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__17);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__18);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__19);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__20);
l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21 = _init_l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5____closed__21);
if (builtin) {res = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__12);
l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__13);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__1();
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__2___closed__2);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__3);
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__4();
l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Elab_Tactic_NormCast_proveEqUsingDown___spec__1___lambda__4___closed__5();
l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__1);
l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__2);
l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__3);
l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lambda__1___closed__4);
l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__2);
l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___closed__1);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8);
l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9 = _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__9);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__1);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__2);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__3);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__4);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__5);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__6);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__1___closed__7);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__1);
l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lambda__3___closed__2);
l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__1);
l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_prove___lambda__1___closed__2);
l_Lean_Elab_Tactic_NormCast_prove___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_prove___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_prove___closed__1);
l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1);
l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__2);
l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__1);
l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_numeralToCoe___lambda__1___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__1);
l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__7___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__1);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__3);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__4);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__5);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__6);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__7);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__8);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__9);
l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__8___closed__10);
l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__1);
l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__3);
l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__10___closed__4);
l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__1);
l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__3);
l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__12___closed__4);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__1);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__2);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__3);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__4);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__5);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__6);
l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_derive___lambda__13___closed__7);
l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__1);
l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__2);
l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__3);
l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___lambda__2___closed__4);
l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1);
l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_normCastTarget___closed__1);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__1);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lambda__4___closed__2);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3);
l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__1);
l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12);
l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13 = _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
