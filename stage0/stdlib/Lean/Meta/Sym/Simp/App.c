// Lean compiler output
// Module: Lean.Meta.Sym.Simp.App
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.SynthInstance import Lean.Meta.Tactic.Simp.Types import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.CongrInfo
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
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0;
lean_object* l_Lean_Meta_Sym_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0;
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0;
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
static lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1;
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_app___override(x_1, x_2);
x_12 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_Meta_Sym_inferType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_11);
x_12 = l_Lean_Meta_Sym_getLevel(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Meta_Sym_inferType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_15);
x_16 = l_Lean_Meta_Sym_getLevel(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_mkConst(x_3, x_21);
x_23 = l_Lean_mkAppB(x_22, x_11, x_15);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_3, x_27);
x_29 = l_Lean_mkAppB(x_28, x_11, x_15);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_14;
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun'", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_19, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkApp4(x_22, x_3, x_15, x_2, x_16);
x_24 = 0;
lean_ctor_set(x_5, 1, x_23);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_mkApp4(x_25, x_3, x_15, x_2, x_16);
x_27 = 0;
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_5);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_35);
lean_inc_ref(x_2);
x_37 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_39, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_Lean_mkApp4(x_41, x_3, x_35, x_2, x_36);
x_44 = 0;
x_45 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_48 = x_40;
} else {
 lean_dec_ref(x_40);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_51 = x_37;
} else {
 lean_dec_ref(x_37);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_53; 
lean_dec_ref(x_5);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_54);
x_56 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_54, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
lean_inc_ref(x_3);
x_59 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_58, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lean_mkApp4(x_61, x_2, x_54, x_55, x_3);
x_63 = 0;
lean_ctor_set(x_4, 1, x_62);
lean_ctor_set(x_4, 0, x_57);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_63);
lean_ctor_set(x_59, 0, x_4);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = l_Lean_mkApp4(x_64, x_2, x_54, x_55, x_3);
x_66 = 0;
lean_ctor_set(x_4, 1, x_65);
lean_ctor_set(x_4, 0, x_57);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_66);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_4);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_57);
lean_free_object(x_4);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_4);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_56);
if (x_71 == 0)
{
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_4, 0);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_74);
x_76 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_74, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
lean_inc_ref(x_3);
x_79 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_78, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = l_Lean_mkApp4(x_80, x_2, x_74, x_75, x_3);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_90 = x_76;
} else {
 lean_dec_ref(x_76);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_4);
x_94 = !lean_is_exclusive(x_5);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_5, 0);
x_96 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_95);
lean_inc_ref(x_92);
x_97 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_92, x_95, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
lean_inc_ref(x_3);
x_100 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_99, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = l_Lean_mkApp6(x_102, x_2, x_92, x_3, x_95, x_93, x_96);
x_104 = 0;
lean_ctor_set(x_5, 1, x_103);
lean_ctor_set(x_5, 0, x_98);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_104);
lean_ctor_set(x_100, 0, x_5);
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = l_Lean_mkApp6(x_105, x_2, x_92, x_3, x_95, x_93, x_96);
x_107 = 0;
lean_ctor_set(x_5, 1, x_106);
lean_ctor_set(x_5, 0, x_98);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_107);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_5);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_98);
lean_free_object(x_5);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_5);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_97);
if (x_112 == 0)
{
return x_97;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_5, 0);
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_115);
lean_inc_ref(x_92);
x_117 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_92, x_115, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
lean_inc_ref(x_3);
x_120 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_119, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l_Lean_mkApp6(x_121, x_2, x_92, x_3, x_115, x_93, x_116);
x_124 = 0;
x_125 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_124);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_118);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_128 = x_120;
} else {
 lean_dec_ref(x_120);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_117, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_131 = x_117;
} else {
 lean_dec_ref(x_117);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
return x_132;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_mkCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to build congruence proof, function expected", 51, 51);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_13 = l_Lean_Meta_Sym_inferType(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_15 = l_Lean_Meta_whnfD(x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 7)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_19 = l_Lean_Meta_Sym_inferType(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_20);
x_21 = l_Lean_Meta_Sym_getLevel(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_23 = l_Lean_Meta_Sym_inferType(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_25 = l_Lean_Meta_Sym_getLevel(x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc_ref(x_3);
lean_inc_ref(x_4);
x_27 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(x_4, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = 0;
lean_inc(x_20);
x_31 = l_Lean_mkLambda(x_17, x_30, x_20, x_18);
x_32 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_mkConst(x_32, x_35);
x_37 = l_Lean_mkApp6(x_36, x_20, x_31, x_2, x_4, x_5, x_3);
x_38 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_6);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
x_40 = 0;
lean_inc(x_20);
x_41 = l_Lean_mkLambda(x_17, x_40, x_20, x_18);
x_42 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_mkConst(x_42, x_45);
x_47 = l_Lean_mkApp6(x_46, x_20, x_41, x_2, x_4, x_5, x_3);
x_48 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_6);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
return x_27;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_27, 0);
lean_inc(x_51);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_25, 0);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_23, 0);
lean_inc(x_57);
lean_dec(x_23);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
return x_21;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_21, 0);
lean_inc(x_60);
lean_dec(x_21);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_19, 0);
lean_inc(x_63);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_65 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
x_66 = l_Lean_indentExpr(x_2);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_67, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
lean_dec(x_15);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
return x_13;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
lean_dec(x_13);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.App", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.simpOverApplied.visit", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(120u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_15);
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_1, x_15, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_15);
x_21 = l_Lean_Meta_Sym_inferType(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_23 = l_Lean_Meta_whnfD(x_22, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; lean_object* x_27; uint8_t x_40; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
x_40 = l_Lean_Expr_hasLooseBVars(x_27);
lean_dec_ref(x_27);
if (x_40 == 0)
{
lean_free_object(x_23);
goto block_39;
}
else
{
if (x_14 == 0)
{
lean_dec_ref(x_26);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_41; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
lean_ctor_set_uint8(x_20, 0, x_14);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_42; 
lean_dec(x_20);
x_42 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_42, 0, x_14);
lean_ctor_set(x_23, 0, x_42);
return x_23;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_23);
x_43 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_20);
x_45 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_15, x_16, x_43, x_44, x_14, x_7, x_8, x_9, x_10, x_11);
return x_45;
}
}
else
{
lean_free_object(x_23);
goto block_39;
}
}
block_39:
{
lean_object* x_28; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_28 = l_Lean_Meta_isProp(x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_31 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_15, x_16, x_20, x_32, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
else
{
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_34 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_34, 0, x_14);
x_35 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_15, x_16, x_20, x_34, x_7, x_8, x_9, x_10, x_11);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_2);
x_46 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
x_47 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
lean_dec(x_23);
if (lean_obj_tag(x_48) == 7)
{
lean_object* x_49; lean_object* x_50; uint8_t x_63; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_48);
x_63 = l_Lean_Expr_hasLooseBVars(x_50);
lean_dec_ref(x_50);
if (x_63 == 0)
{
goto block_62;
}
else
{
if (x_14 == 0)
{
lean_dec_ref(x_49);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_20)) {
 x_64 = x_20;
} else {
 lean_dec_ref(x_20);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 0, 1);
} else {
 x_65 = x_64;
}
lean_ctor_set_uint8(x_65, 0, x_14);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_20);
x_69 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_15, x_16, x_67, x_68, x_14, x_7, x_8, x_9, x_10, x_11);
return x_69;
}
}
else
{
goto block_62;
}
}
block_62:
{
lean_object* x_51; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_51 = l_Lean_Meta_isProp(x_49, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_54 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_15, x_16, x_20, x_55, x_7, x_8, x_9, x_10, x_11);
return x_56;
}
else
{
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_54;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_57 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_57, 0, x_14);
x_58 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_15, x_16, x_20, x_57, x_7, x_8, x_9, x_10, x_11);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_48);
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_2);
x_70 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3;
x_71 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
return x_23;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
lean_dec(x_23);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_21, 0);
lean_inc(x_76);
lean_dec(x_21);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_19;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_78 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4;
x_79 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_78, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_79;
}
}
else
{
lean_object* x_80; 
x_80 = lean_apply_10(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_80;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_simpOverApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.propagateOverApplied.visit", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(166u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_15);
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_1, x_15, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
lean_dec_ref(x_20);
x_24 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_15, x_16, x_21, x_22, x_23, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_19;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1;
x_26 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_apply_10(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function type expected", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isForall(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_whnfD(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_isForall(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1;
x_13 = l_Lean_MessageData_ofExpr(x_10);
x_14 = l_Lean_indentD(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_15, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_10, x_2);
return x_20;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
else
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0;
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
x_19 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1;
x_20 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2;
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
x_37 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
x_38 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
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
x_46 = l_Lean_instInhabitedExpr;
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, lean_box(0));
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
x_54 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
x_55 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
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
x_64 = l_Lean_instInhabitedExpr;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, lean_box(0));
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
x_74 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
x_75 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
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
x_85 = l_Lean_instInhabitedExpr;
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, lean_box(0));
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
x_93 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1;
x_94 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2;
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
x_110 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
x_111 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
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
x_121 = l_Lean_instInhabitedExpr;
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, lean_box(0));
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
x_131 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1;
x_132 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2;
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
x_149 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3;
x_150 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4;
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
x_160 = l_Lean_instInhabitedExpr;
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_163;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.getFnType", 62, 62);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(197u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 1)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_inferType(x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
x_14 = l_Lean_Expr_appFn_x21(x_1);
lean_dec_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_14, x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_20);
lean_dec_ref(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_17);
lean_dec(x_19);
x_21 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
x_22 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_21, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 7)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
x_26 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1;
x_27 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(x_26, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_17;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_app___override(x_1, x_2);
x_12 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpFixedPrefix.go", 71, 71);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(257u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(249u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_unsigned_to_nat(264u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_unsigned_to_nat(244u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
x_2 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_14);
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_17, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_15);
x_23 = lean_sym_simp(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_24; 
lean_dec(x_22);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_ctor_set_uint8(x_25, 0, x_13);
x_27 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_28, 0, x_13);
x_29 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_28);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_23);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_14);
x_33 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_14, x_17, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_35 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_34, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_38);
lean_dec_ref(x_36);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_31);
lean_inc_ref(x_14);
x_39 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_14, x_31, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_37);
x_41 = l_Lean_Meta_Sym_getLevel(x_37, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc_ref(x_38);
x_43 = l_Lean_Meta_Sym_getLevel(x_38, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_mkConst(x_46, x_49);
lean_inc_ref(x_38);
x_51 = l_Lean_mkApp6(x_50, x_37, x_38, x_15, x_31, x_14, x_32);
lean_ctor_set(x_25, 1, x_51);
lean_ctor_set(x_25, 0, x_40);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_43, 0, x_19);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
lean_dec(x_43);
x_53 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_mkConst(x_53, x_56);
lean_inc_ref(x_38);
x_58 = l_Lean_mkApp6(x_57, x_37, x_38, x_15, x_31, x_14, x_32);
lean_ctor_set(x_25, 1, x_58);
lean_ctor_set(x_25, 0, x_40);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_25);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_19);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
return x_43;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_43, 0);
lean_inc(x_61);
lean_dec(x_43);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_39);
if (x_66 == 0)
{
return x_39;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_39, 0);
lean_inc(x_67);
lean_dec(x_39);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_69 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_70 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_35);
if (x_71 == 0)
{
return x_35;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_35, 0);
lean_inc(x_72);
lean_dec(x_35);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_25);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_33);
if (x_74 == 0)
{
return x_33;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_33, 0);
lean_inc(x_75);
lean_dec(x_33);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_25, 0);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_25);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_14);
x_79 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_14, x_17, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_81 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_80, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
if (lean_obj_tag(x_82) == 7)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_83 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_82, 2);
lean_inc_ref(x_84);
lean_dec_ref(x_82);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_77);
lean_inc_ref(x_14);
x_85 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_14, x_77, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_83);
x_87 = l_Lean_Meta_Sym_getLevel(x_83, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc_ref(x_84);
x_89 = l_Lean_Meta_Sym_getLevel(x_84, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_mkConst(x_92, x_95);
lean_inc_ref(x_84);
x_97 = l_Lean_mkApp6(x_96, x_83, x_84, x_15, x_77, x_14, x_78);
x_98 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_84);
lean_ctor_set(x_19, 0, x_98);
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_19);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_101 = x_89;
} else {
 lean_dec_ref(x_89);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_86);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_104 = x_87;
} else {
 lean_dec_ref(x_87);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_106 = lean_ctor_get(x_85, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_107 = x_85;
} else {
 lean_dec_ref(x_85);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_82);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_109 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_110 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_81, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_112 = x_81;
} else {
 lean_dec_ref(x_81);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_114 = lean_ctor_get(x_79, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_115 = x_79;
} else {
 lean_dec_ref(x_79);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_23, 0);
lean_inc(x_117);
lean_dec(x_23);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_117)) {
 x_118 = x_117;
} else {
 lean_dec_ref(x_117);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 0, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set_uint8(x_119, 0, x_13);
x_120 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
lean_ctor_set(x_19, 1, x_120);
lean_ctor_set(x_19, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_19);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_14);
x_125 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_14, x_17, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_127 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_126, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
if (lean_obj_tag(x_128) == 7)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_129 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_128, 2);
lean_inc_ref(x_130);
lean_dec_ref(x_128);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_122);
lean_inc_ref(x_14);
x_131 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_14, x_122, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_129);
x_133 = l_Lean_Meta_Sym_getLevel(x_129, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
lean_inc_ref(x_130);
x_135 = l_Lean_Meta_Sym_getLevel(x_130, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_mkConst(x_138, x_141);
lean_inc_ref(x_130);
x_143 = l_Lean_mkApp6(x_142, x_129, x_130, x_15, x_122, x_14, x_123);
if (lean_is_scalar(x_124)) {
 x_144 = lean_alloc_ctor(1, 2, 1);
} else {
 x_144 = x_124;
}
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_130);
lean_ctor_set(x_19, 0, x_144);
if (lean_is_scalar(x_137)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_137;
}
lean_ctor_set(x_145, 0, x_19);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_147 = x_135;
} else {
 lean_dec_ref(x_135);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_132);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_149 = lean_ctor_get(x_133, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_150 = x_133;
} else {
 lean_dec_ref(x_133);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_152 = lean_ctor_get(x_131, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_153 = x_131;
} else {
 lean_dec_ref(x_131);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_155 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_156 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_127, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_158 = x_127;
} else {
 lean_dec_ref(x_127);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_160 = lean_ctor_get(x_125, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_161 = x_125;
} else {
 lean_dec_ref(x_125);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_17);
x_163 = lean_ctor_get(x_23, 0);
lean_inc(x_163);
lean_dec_ref(x_23);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
lean_dec_ref(x_163);
x_164 = !lean_is_exclusive(x_21);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_21, 0);
x_166 = lean_ctor_get(x_21, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_167 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_22, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
if (lean_obj_tag(x_168) == 7)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_169 = lean_ctor_get(x_168, 1);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_168, 2);
lean_inc_ref(x_170);
lean_dec_ref(x_168);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_165);
x_171 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_165, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_169);
x_173 = l_Lean_Meta_Sym_getLevel(x_169, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
lean_inc_ref(x_170);
x_175 = l_Lean_Meta_Sym_getLevel(x_170, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_mkConst(x_178, x_181);
lean_inc_ref(x_170);
x_183 = l_Lean_mkApp6(x_182, x_169, x_170, x_14, x_165, x_166, x_15);
lean_ctor_set(x_21, 1, x_183);
lean_ctor_set(x_21, 0, x_172);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_170);
lean_ctor_set(x_175, 0, x_19);
return x_175;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_175, 0);
lean_inc(x_184);
lean_dec(x_175);
x_185 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_174);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_mkConst(x_185, x_188);
lean_inc_ref(x_170);
x_190 = l_Lean_mkApp6(x_189, x_169, x_170, x_14, x_165, x_166, x_15);
lean_ctor_set(x_21, 1, x_190);
lean_ctor_set(x_21, 0, x_172);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_170);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_19);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_174);
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_free_object(x_21);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_192 = !lean_is_exclusive(x_175);
if (x_192 == 0)
{
return x_175;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_175, 0);
lean_inc(x_193);
lean_dec(x_175);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_free_object(x_21);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_195 = !lean_is_exclusive(x_173);
if (x_195 == 0)
{
return x_173;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_173, 0);
lean_inc(x_196);
lean_dec(x_173);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_free_object(x_21);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_198 = !lean_is_exclusive(x_171);
if (x_198 == 0)
{
return x_171;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_171, 0);
lean_inc(x_199);
lean_dec(x_171);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_168);
lean_free_object(x_21);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_201 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_202 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_201, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_202;
}
}
else
{
uint8_t x_203; 
lean_free_object(x_21);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_203 = !lean_is_exclusive(x_167);
if (x_203 == 0)
{
return x_167;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_167, 0);
lean_inc(x_204);
lean_dec(x_167);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_21, 0);
x_207 = lean_ctor_get(x_21, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_21);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_208 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_22, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
if (lean_obj_tag(x_209) == 7)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_210 = lean_ctor_get(x_209, 1);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_209, 2);
lean_inc_ref(x_211);
lean_dec_ref(x_209);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_206);
x_212 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_206, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_210);
x_214 = l_Lean_Meta_Sym_getLevel(x_210, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
lean_inc_ref(x_211);
x_216 = l_Lean_Meta_Sym_getLevel(x_211, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
x_219 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_215);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_mkConst(x_219, x_222);
lean_inc_ref(x_211);
x_224 = l_Lean_mkApp6(x_223, x_210, x_211, x_14, x_206, x_207, x_15);
x_225 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_225, 0, x_213);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_211);
lean_ctor_set(x_19, 0, x_225);
if (lean_is_scalar(x_218)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_218;
}
lean_ctor_set(x_226, 0, x_19);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_215);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_228 = x_216;
} else {
 lean_dec_ref(x_216);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_230 = lean_ctor_get(x_214, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_231 = x_214;
} else {
 lean_dec_ref(x_214);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_233 = lean_ctor_get(x_212, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_234 = x_212;
} else {
 lean_dec_ref(x_212);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_209);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_236 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_237 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_236, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_238 = lean_ctor_get(x_208, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_239 = x_208;
} else {
 lean_dec_ref(x_208);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_241);
x_242 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_242);
lean_dec_ref(x_21);
x_243 = !lean_is_exclusive(x_163);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_163, 0);
x_245 = lean_ctor_get(x_163, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_246 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_22, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
if (lean_obj_tag(x_247) == 7)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_248 = lean_ctor_get(x_247, 1);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_247, 2);
lean_inc_ref(x_249);
lean_dec_ref(x_247);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_244);
lean_inc_ref(x_241);
x_250 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_241, x_244, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_248);
x_252 = l_Lean_Meta_Sym_getLevel(x_248, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
lean_inc_ref(x_249);
x_254 = l_Lean_Meta_Sym_getLevel(x_249, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
x_258 = lean_box(0);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_253);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_mkConst(x_257, x_260);
lean_inc_ref(x_249);
x_262 = l_Lean_mkApp8(x_261, x_248, x_249, x_14, x_241, x_15, x_244, x_242, x_245);
lean_ctor_set(x_163, 1, x_262);
lean_ctor_set(x_163, 0, x_251);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_249);
lean_ctor_set(x_19, 0, x_163);
lean_ctor_set(x_254, 0, x_19);
return x_254;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_263 = lean_ctor_get(x_254, 0);
lean_inc(x_263);
lean_dec(x_254);
x_264 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
x_265 = lean_box(0);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_253);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_mkConst(x_264, x_267);
lean_inc_ref(x_249);
x_269 = l_Lean_mkApp8(x_268, x_248, x_249, x_14, x_241, x_15, x_244, x_242, x_245);
lean_ctor_set(x_163, 1, x_269);
lean_ctor_set(x_163, 0, x_251);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_249);
lean_ctor_set(x_19, 0, x_163);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_19);
return x_270;
}
}
else
{
uint8_t x_271; 
lean_dec(x_253);
lean_dec(x_251);
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_free_object(x_163);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_271 = !lean_is_exclusive(x_254);
if (x_271 == 0)
{
return x_254;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_254, 0);
lean_inc(x_272);
lean_dec(x_254);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_251);
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_free_object(x_163);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_274 = !lean_is_exclusive(x_252);
if (x_274 == 0)
{
return x_252;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_252, 0);
lean_inc(x_275);
lean_dec(x_252);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_free_object(x_163);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_277 = !lean_is_exclusive(x_250);
if (x_277 == 0)
{
return x_250;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_250, 0);
lean_inc(x_278);
lean_dec(x_250);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_247);
lean_free_object(x_163);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_280 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_281 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_280, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_281;
}
}
else
{
uint8_t x_282; 
lean_free_object(x_163);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_282 = !lean_is_exclusive(x_246);
if (x_282 == 0)
{
return x_246;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_246, 0);
lean_inc(x_283);
lean_dec(x_246);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_163, 0);
x_286 = lean_ctor_get(x_163, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_163);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_287 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_22, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
if (lean_obj_tag(x_288) == 7)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_289 = lean_ctor_get(x_288, 1);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_288, 2);
lean_inc_ref(x_290);
lean_dec_ref(x_288);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_285);
lean_inc_ref(x_241);
x_291 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_241, x_285, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_289);
x_293 = l_Lean_Meta_Sym_getLevel(x_289, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec_ref(x_293);
lean_inc_ref(x_290);
x_295 = l_Lean_Meta_Sym_getLevel(x_290, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_294);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_mkConst(x_298, x_301);
lean_inc_ref(x_290);
x_303 = l_Lean_mkApp8(x_302, x_289, x_290, x_14, x_241, x_15, x_285, x_242, x_286);
x_304 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_304, 0, x_292);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_13);
lean_ctor_set(x_19, 1, x_290);
lean_ctor_set(x_19, 0, x_304);
if (lean_is_scalar(x_297)) {
 x_305 = lean_alloc_ctor(0, 1, 0);
} else {
 x_305 = x_297;
}
lean_ctor_set(x_305, 0, x_19);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_294);
lean_dec(x_292);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_306 = lean_ctor_get(x_295, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_307 = x_295;
} else {
 lean_dec_ref(x_295);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_292);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_310 = x_293;
} else {
 lean_dec_ref(x_293);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_312 = lean_ctor_get(x_291, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_313 = x_291;
} else {
 lean_dec_ref(x_291);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_288);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_315 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_316 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_315, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_free_object(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_317 = lean_ctor_get(x_287, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_318 = x_287;
} else {
 lean_dec_ref(x_287);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_317);
return x_319;
}
}
}
}
}
else
{
uint8_t x_320; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_320 = !lean_is_exclusive(x_23);
if (x_320 == 0)
{
return x_23;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_23, 0);
lean_inc(x_321);
lean_dec(x_23);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_19, 0);
x_324 = lean_ctor_get(x_19, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_15);
x_325 = lean_sym_simp(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_325) == 0)
{
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_324);
lean_dec_ref(x_323);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_326)) {
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 0, 1);
} else {
 x_329 = x_328;
}
lean_ctor_set_uint8(x_329, 0, x_13);
x_330 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2;
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
if (lean_is_scalar(x_327)) {
 x_332 = lean_alloc_ctor(0, 1, 0);
} else {
 x_332 = x_327;
}
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_327);
x_333 = lean_ctor_get(x_326, 0);
lean_inc_ref(x_333);
x_334 = lean_ctor_get(x_326, 1);
lean_inc_ref(x_334);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_335 = x_326;
} else {
 lean_dec_ref(x_326);
 x_335 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_14);
x_336 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(x_14, x_17, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec_ref(x_336);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_338 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_337, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
if (lean_obj_tag(x_339) == 7)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_340 = lean_ctor_get(x_339, 1);
lean_inc_ref(x_340);
x_341 = lean_ctor_get(x_339, 2);
lean_inc_ref(x_341);
lean_dec_ref(x_339);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_333);
lean_inc_ref(x_14);
x_342 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_14, x_333, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_340);
x_344 = l_Lean_Meta_Sym_getLevel(x_340, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec_ref(x_344);
lean_inc_ref(x_341);
x_346 = l_Lean_Meta_Sym_getLevel(x_341, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
x_349 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
x_350 = lean_box(0);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_345);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Lean_mkConst(x_349, x_352);
lean_inc_ref(x_341);
x_354 = l_Lean_mkApp6(x_353, x_340, x_341, x_15, x_333, x_14, x_334);
if (lean_is_scalar(x_335)) {
 x_355 = lean_alloc_ctor(1, 2, 1);
} else {
 x_355 = x_335;
}
lean_ctor_set(x_355, 0, x_343);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_13);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_341);
if (lean_is_scalar(x_348)) {
 x_357 = lean_alloc_ctor(0, 1, 0);
} else {
 x_357 = x_348;
}
lean_ctor_set(x_357, 0, x_356);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_358 = lean_ctor_get(x_346, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_343);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_361 = lean_ctor_get(x_344, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_362 = x_344;
} else {
 lean_dec_ref(x_344);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_364 = lean_ctor_get(x_342, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_365 = x_342;
} else {
 lean_dec_ref(x_342);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_367 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4;
x_368 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_367, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_369 = lean_ctor_get(x_338, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_370 = x_338;
} else {
 lean_dec_ref(x_338);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_369);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_372 = lean_ctor_get(x_336, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_373 = x_336;
} else {
 lean_dec_ref(x_336);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_372);
return x_374;
}
}
}
else
{
lean_object* x_375; 
lean_dec(x_17);
x_375 = lean_ctor_get(x_325, 0);
lean_inc(x_375);
lean_dec_ref(x_325);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_375);
x_376 = lean_ctor_get(x_323, 0);
lean_inc_ref(x_376);
x_377 = lean_ctor_get(x_323, 1);
lean_inc_ref(x_377);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_378 = x_323;
} else {
 lean_dec_ref(x_323);
 x_378 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_379 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_324, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
if (lean_obj_tag(x_380) == 7)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_381 = lean_ctor_get(x_380, 1);
lean_inc_ref(x_381);
x_382 = lean_ctor_get(x_380, 2);
lean_inc_ref(x_382);
lean_dec_ref(x_380);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_376);
x_383 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_376, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
lean_dec_ref(x_383);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_381);
x_385 = l_Lean_Meta_Sym_getLevel(x_381, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec_ref(x_385);
lean_inc_ref(x_382);
x_387 = l_Lean_Meta_Sym_getLevel(x_382, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
x_390 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
x_391 = lean_box(0);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_386);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_mkConst(x_390, x_393);
lean_inc_ref(x_382);
x_395 = l_Lean_mkApp6(x_394, x_381, x_382, x_14, x_376, x_377, x_15);
if (lean_is_scalar(x_378)) {
 x_396 = lean_alloc_ctor(1, 2, 1);
} else {
 x_396 = x_378;
}
lean_ctor_set(x_396, 0, x_384);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set_uint8(x_396, sizeof(void*)*2, x_13);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_382);
if (lean_is_scalar(x_389)) {
 x_398 = lean_alloc_ctor(0, 1, 0);
} else {
 x_398 = x_389;
}
lean_ctor_set(x_398, 0, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_386);
lean_dec(x_384);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_376);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_399 = lean_ctor_get(x_387, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_400 = x_387;
} else {
 lean_dec_ref(x_387);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 1, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_384);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_376);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_402 = lean_ctor_get(x_385, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_403 = x_385;
} else {
 lean_dec_ref(x_385);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_376);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_405 = lean_ctor_get(x_383, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_406 = x_383;
} else {
 lean_dec_ref(x_383);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_405);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_376);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_408 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5;
x_409 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_408, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_378);
lean_dec_ref(x_377);
lean_dec_ref(x_376);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_410 = lean_ctor_get(x_379, 0);
lean_inc(x_410);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_411 = x_379;
} else {
 lean_dec_ref(x_379);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 1, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_410);
return x_412;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_413 = lean_ctor_get(x_323, 0);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_323, 1);
lean_inc_ref(x_414);
lean_dec_ref(x_323);
x_415 = lean_ctor_get(x_375, 0);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_375, 1);
lean_inc_ref(x_416);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_417 = x_375;
} else {
 lean_dec_ref(x_375);
 x_417 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_418 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(x_324, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
if (lean_obj_tag(x_419) == 7)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_420 = lean_ctor_get(x_419, 1);
lean_inc_ref(x_420);
x_421 = lean_ctor_get(x_419, 2);
lean_inc_ref(x_421);
lean_dec_ref(x_419);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_415);
lean_inc_ref(x_413);
x_422 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(x_413, x_415, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_420);
x_424 = l_Lean_Meta_Sym_getLevel(x_420, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
lean_dec_ref(x_424);
lean_inc_ref(x_421);
x_426 = l_Lean_Meta_Sym_getLevel(x_421, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
x_429 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
x_430 = lean_box(0);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_430);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_425);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_mkConst(x_429, x_432);
lean_inc_ref(x_421);
x_434 = l_Lean_mkApp8(x_433, x_420, x_421, x_14, x_413, x_15, x_415, x_414, x_416);
if (lean_is_scalar(x_417)) {
 x_435 = lean_alloc_ctor(1, 2, 1);
} else {
 x_435 = x_417;
}
lean_ctor_set(x_435, 0, x_423);
lean_ctor_set(x_435, 1, x_434);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_13);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_421);
if (lean_is_scalar(x_428)) {
 x_437 = lean_alloc_ctor(0, 1, 0);
} else {
 x_437 = x_428;
}
lean_ctor_set(x_437, 0, x_436);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_425);
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec_ref(x_420);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_438 = lean_ctor_get(x_426, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_439 = x_426;
} else {
 lean_dec_ref(x_426);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec_ref(x_420);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_441 = lean_ctor_get(x_424, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 x_442 = x_424;
} else {
 lean_dec_ref(x_424);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec_ref(x_421);
lean_dec_ref(x_420);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_444 = lean_ctor_get(x_422, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 x_445 = x_422;
} else {
 lean_dec_ref(x_422);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_419);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_447 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6;
x_448 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_447, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_449 = lean_ctor_get(x_418, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_450 = x_418;
} else {
 lean_dec_ref(x_418);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_452 = lean_ctor_get(x_325, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_453 = x_325;
} else {
 lean_dec_ref(x_325);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec_ref(x_2);
x_455 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7;
x_456 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(x_455, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_457 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
x_458 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_458, 0, x_457);
return x_458;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_nat_dec_le(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_add(x_2, x_3);
x_16 = lean_nat_dec_lt(x_15, x_13);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(x_17, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_20 = lean_nat_sub(x_19, x_3);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed), 11, 1);
lean_closure_set(x_21, 0, x_3);
x_22 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_21, x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_23 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpInterlaced.go", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(299u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_15);
x_19 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_18, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_array_fget_borrowed(x_1, x_18);
lean_dec(x_18);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_24; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_21, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 0, 1);
x_27 = lean_unbox(x_22);
lean_ctor_set_uint8(x_26, 0, x_27);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_free_object(x_19);
x_28 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_21);
x_30 = lean_unbox(x_22);
x_31 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_15, x_16, x_28, x_29, x_30, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_free_object(x_19);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_32 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_15, x_16, x_21, x_33, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_32;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_array_fget_borrowed(x_1, x_18);
lean_dec(x_18);
x_37 = lean_unbox(x_36);
if (x_37 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
if (lean_is_exclusive(x_35)) {
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 0, 1);
} else {
 x_39 = x_38;
}
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, 0, x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_35);
x_44 = lean_unbox(x_36);
x_45 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_15, x_16, x_42, x_43, x_44, x_7, x_8, x_9, x_10, x_11);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_46 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_15, x_16, x_35, x_47, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
else
{
lean_dec(x_35);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_46;
}
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_19;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_3);
x_49 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1;
x_50 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_51 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_15, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(x_2, x_12, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
lean_dec_ref(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed), 12, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_15);
x_19 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_18, x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
lean_object* x_7; 
x_7 = lean_array_push(x_1, x_3);
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_array_push(x_1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_11 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_12 = lean_mk_array(x_2, x_11);
x_13 = lean_array_push(x_12, x_3);
return x_13;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm.simpEqArgs", 81, 81);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(412u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_array_get_borrowed(x_32, x_1, x_4);
x_34 = lean_unbox(x_33);
switch (x_34) {
case 5:
{
lean_dec_ref(x_17);
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
x_26 = lean_box(0);
goto block_30;
}
case 0:
{
lean_dec_ref(x_17);
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
x_26 = lean_box(0);
goto block_30;
}
case 3:
{
lean_dec_ref(x_17);
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
x_26 = lean_box(0);
goto block_30;
}
case 2:
{
lean_object* x_35; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_35 = lean_sym_simp(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_4, x_37);
lean_dec(x_4);
x_39 = lean_nat_add(x_5, x_37);
x_40 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(x_6, x_5, x_36);
x_3 = x_16;
x_4 = x_38;
x_5 = x_39;
x_6 = x_40;
goto _start;
}
else
{
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_35;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_42 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1;
x_43 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_43;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_4, x_27);
lean_dec(x_4);
x_3 = x_16;
x_4 = x_28;
x_7 = x_18;
x_8 = x_19;
x_9 = x_20;
x_10 = x_21;
x_11 = x_22;
x_12 = x_23;
x_13 = x_24;
x_14 = x_25;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = l_Array_isEmpty___redArg(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Array_reverse___redArg(x_6);
x_46 = lean_apply_10(x_2, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_47 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; uint8_t x_13; 
x_6 = 1;
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 3)
{
x_7 = x_1;
goto block_11;
}
else
{
x_7 = x_5;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.App.0.Lean.Meta.Sym.Simp.simpUsingCongrThm", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(392u);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_31 = x_25;
} else {
 lean_dec_ref(x_25);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_38 = x_29;
} else {
 lean_dec_ref(x_29);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
x_41 = lean_ctor_get(x_30, 2);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_35)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_35;
}
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_33)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_33;
}
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_31)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_31;
}
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_26)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_26;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_95; 
x_50 = lean_ctor_get(x_30, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_30, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_30, 0);
lean_dec(x_52);
x_53 = lean_array_uget(x_4, x_6);
x_54 = lean_array_fget(x_39, x_40);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_40, x_55);
lean_dec(x_40);
lean_ctor_set(x_30, 1, x_56);
lean_inc(x_53);
x_85 = l_Lean_Expr_app___override(x_34, x_53);
x_86 = l_Lean_Expr_bindingBody_x21(x_37);
lean_dec(x_37);
x_95 = lean_unbox(x_54);
lean_dec(x_54);
switch (x_95) {
case 0:
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_87 = lean_box(0);
goto block_94;
}
case 3:
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_87 = lean_box(0);
goto block_94;
}
case 5:
{
lean_object* x_96; lean_object* x_97; 
lean_inc(x_53);
x_96 = lean_array_push(x_36, x_53);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_53);
x_97 = l_Lean_Meta_Sym_inferType(x_53, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Expr_bindingDomain_x21(x_86);
x_100 = lean_expr_instantiate_rev(x_99, x_96);
lean_dec_ref(x_99);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_100);
x_101 = l_Lean_Meta_isDefEqI(x_98, x_100, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_53);
x_104 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_105 = l_Lean_Meta_trySynthInstance(x_100, x_104, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; 
lean_free_object(x_105);
lean_dec(x_102);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_108;
x_61 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_107);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 0, 1);
x_110 = lean_unbox(x_102);
lean_dec(x_102);
lean_ctor_set_uint8(x_109, 0, x_110);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_96);
lean_ctor_set(x_112, 1, x_86);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_85);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_32);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_30);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_105, 0, x_116);
return x_105;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
lean_dec(x_105);
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_118; 
lean_dec(x_102);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_118;
x_61 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_119 = lean_alloc_ctor(0, 0, 1);
x_120 = lean_unbox(x_102);
lean_dec(x_102);
lean_ctor_set_uint8(x_119, 0, x_120);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_96);
lean_ctor_set(x_122, 1, x_86);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_85);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_32);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_30);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_102);
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_30);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_105);
if (x_128 == 0)
{
return x_105;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_105, 0);
lean_inc(x_129);
lean_dec(x_105);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
lean_dec(x_102);
lean_dec_ref(x_100);
x_57 = x_85;
x_58 = x_96;
x_59 = x_86;
x_60 = x_53;
x_61 = lean_box(0);
goto block_70;
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_100);
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_30);
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_101);
if (x_131 == 0)
{
return x_101;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_101, 0);
lean_inc(x_132);
lean_dec(x_101);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec_ref(x_96);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_30);
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_97);
if (x_134 == 0)
{
return x_97;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_97, 0);
lean_inc(x_135);
lean_dec(x_97);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
case 2:
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_inc(x_53);
x_137 = lean_array_push(x_36, x_53);
lean_inc_ref(x_2);
x_138 = lean_array_get_borrowed(x_2, x_3, x_32);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_53);
x_139 = l_Lean_Meta_Sym_mkEqRefl(x_53, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
lean_inc(x_140);
lean_inc(x_53);
x_141 = l_Lean_mkAppB(x_85, x_53, x_140);
x_142 = lean_array_push(x_137, x_53);
x_143 = lean_array_push(x_142, x_140);
x_71 = x_32;
x_72 = x_141;
x_73 = x_143;
x_74 = x_86;
x_75 = lean_box(0);
goto block_84;
}
else
{
uint8_t x_144; 
lean_dec_ref(x_137);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_30);
lean_dec(x_53);
lean_dec(x_32);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_139);
if (x_144 == 0)
{
return x_139;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_53);
x_147 = lean_ctor_get(x_138, 0);
x_148 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_148);
lean_inc_ref(x_147);
x_149 = l_Lean_mkAppB(x_85, x_147, x_148);
lean_inc_ref(x_147);
x_150 = lean_array_push(x_137, x_147);
lean_inc_ref(x_148);
x_151 = lean_array_push(x_150, x_148);
x_71 = x_32;
x_72 = x_149;
x_73 = x_151;
x_74 = x_86;
x_75 = lean_box(0);
goto block_84;
}
}
default: 
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_152 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_153 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_152, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_36);
lean_ctor_set(x_154, 1, x_86);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_85);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_32);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_30);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_1);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_157);
x_17 = x_158;
x_18 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_159; 
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_30);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_153);
if (x_159 == 0)
{
return x_153;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_153, 0);
lean_inc(x_160);
lean_dec(x_153);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
block_70:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc_ref(x_60);
x_62 = l_Lean_Expr_app___override(x_57, x_60);
x_63 = lean_array_push(x_58, x_60);
x_64 = l_Lean_Expr_bindingBody_x21(x_59);
lean_dec_ref(x_59);
if (lean_is_scalar(x_38)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_38;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_35)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_35;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_33)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_33;
}
lean_ctor_set(x_67, 0, x_32);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_31)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_31;
}
lean_ctor_set(x_68, 0, x_30);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_1);
if (lean_is_scalar(x_26)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_26;
}
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
x_17 = x_69;
x_18 = lean_box(0);
goto block_22;
}
block_84:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = l_Lean_Expr_bindingBody_x21(x_74);
lean_dec_ref(x_74);
x_77 = l_Lean_Expr_bindingBody_x21(x_76);
lean_dec_ref(x_76);
x_78 = lean_nat_add(x_71, x_55);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_30);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
x_17 = x_83;
x_18 = lean_box(0);
goto block_22;
}
block_94:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_array_push(x_36, x_53);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_32);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_30);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
x_17 = x_93;
x_18 = lean_box(0);
goto block_22;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_205; 
lean_dec(x_30);
x_162 = lean_array_uget(x_4, x_6);
x_163 = lean_array_fget(x_39, x_40);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_add(x_40, x_164);
lean_dec(x_40);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_39);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_41);
lean_inc(x_162);
x_195 = l_Lean_Expr_app___override(x_34, x_162);
x_196 = l_Lean_Expr_bindingBody_x21(x_37);
lean_dec(x_37);
x_205 = lean_unbox(x_163);
lean_dec(x_163);
switch (x_205) {
case 0:
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_197 = lean_box(0);
goto block_204;
}
case 3:
{
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_197 = lean_box(0);
goto block_204;
}
case 5:
{
lean_object* x_206; lean_object* x_207; 
lean_inc(x_162);
x_206 = lean_array_push(x_36, x_162);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_162);
x_207 = l_Lean_Meta_Sym_inferType(x_162, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Expr_bindingDomain_x21(x_196);
x_210 = lean_expr_instantiate_rev(x_209, x_206);
lean_dec_ref(x_209);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_210);
x_211 = l_Lean_Meta_isDefEqI(x_208, x_210, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_unbox(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_162);
x_214 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_215 = l_Lean_Meta_trySynthInstance(x_210, x_214, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
if (lean_obj_tag(x_216) == 1)
{
lean_object* x_218; 
lean_dec(x_217);
lean_dec(x_212);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec_ref(x_216);
x_167 = x_195;
x_168 = x_206;
x_169 = x_196;
x_170 = x_218;
x_171 = lean_box(0);
goto block_180;
}
else
{
lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_216);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_219 = lean_alloc_ctor(0, 0, 1);
x_220 = lean_unbox(x_212);
lean_dec(x_212);
lean_ctor_set_uint8(x_219, 0, x_220);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_206);
lean_ctor_set(x_222, 1, x_196);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_195);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_32);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_166);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_225);
if (lean_is_scalar(x_217)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_217;
}
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_212);
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_228 = lean_ctor_get(x_215, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_229 = x_215;
} else {
 lean_dec_ref(x_215);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
lean_dec(x_212);
lean_dec_ref(x_210);
x_167 = x_195;
x_168 = x_206;
x_169 = x_196;
x_170 = x_162;
x_171 = lean_box(0);
goto block_180;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_210);
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_231 = lean_ctor_get(x_211, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_232 = x_211;
} else {
 lean_dec_ref(x_211);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec_ref(x_206);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_235 = x_207;
} else {
 lean_dec_ref(x_207);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
case 2:
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_inc(x_162);
x_237 = lean_array_push(x_36, x_162);
lean_inc_ref(x_2);
x_238 = lean_array_get_borrowed(x_2, x_3, x_32);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_162);
x_239 = l_Lean_Meta_Sym_mkEqRefl(x_162, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
lean_inc(x_240);
lean_inc(x_162);
x_241 = l_Lean_mkAppB(x_195, x_162, x_240);
x_242 = lean_array_push(x_237, x_162);
x_243 = lean_array_push(x_242, x_240);
x_181 = x_32;
x_182 = x_241;
x_183 = x_243;
x_184 = x_196;
x_185 = lean_box(0);
goto block_194;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_237);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_162);
lean_dec(x_32);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_244 = lean_ctor_get(x_239, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_245 = x_239;
} else {
 lean_dec_ref(x_239);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_162);
x_247 = lean_ctor_get(x_238, 0);
x_248 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_248);
lean_inc_ref(x_247);
x_249 = l_Lean_mkAppB(x_195, x_247, x_248);
lean_inc_ref(x_247);
x_250 = lean_array_push(x_237, x_247);
lean_inc_ref(x_248);
x_251 = lean_array_push(x_250, x_248);
x_181 = x_32;
x_182 = x_249;
x_183 = x_251;
x_184 = x_196;
x_185 = lean_box(0);
goto block_194;
}
}
default: 
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_162);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
x_252 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1;
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_253 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(x_252, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_253);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_36);
lean_ctor_set(x_254, 1, x_196);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_195);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_32);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_166);
lean_ctor_set(x_257, 1, x_256);
lean_inc(x_1);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_257);
x_17 = x_258;
x_18 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_166);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_259 = lean_ctor_get(x_253, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_260 = x_253;
} else {
 lean_dec_ref(x_253);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
}
block_180:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_inc_ref(x_170);
x_172 = l_Lean_Expr_app___override(x_167, x_170);
x_173 = lean_array_push(x_168, x_170);
x_174 = l_Lean_Expr_bindingBody_x21(x_169);
lean_dec_ref(x_169);
if (lean_is_scalar(x_38)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_38;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_35)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_35;
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
if (lean_is_scalar(x_33)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_33;
}
lean_ctor_set(x_177, 0, x_32);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_31)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_31;
}
lean_ctor_set(x_178, 0, x_166);
lean_ctor_set(x_178, 1, x_177);
lean_inc(x_1);
if (lean_is_scalar(x_26)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_26;
}
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_178);
x_17 = x_179;
x_18 = lean_box(0);
goto block_22;
}
block_194:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = l_Lean_Expr_bindingBody_x21(x_184);
lean_dec_ref(x_184);
x_187 = l_Lean_Expr_bindingBody_x21(x_186);
lean_dec_ref(x_186);
x_188 = lean_nat_add(x_181, x_164);
lean_dec(x_181);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_166);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_1);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_1);
lean_ctor_set(x_193, 1, x_192);
x_17 = x_193;
x_18 = lean_box(0);
goto block_22;
}
block_204:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_array_push(x_36, x_162);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_32);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_166);
lean_ctor_set(x_202, 1, x_201);
lean_inc(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_202);
x_17 = x_203;
x_18 = lean_box(0);
goto block_22;
}
}
}
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(393u);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1;
x_30 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2;
x_31 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_31);
x_32 = lean_mk_array(x_31, x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_31, x_33);
lean_dec(x_31);
x_35 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_32, x_34);
x_36 = lean_array_get_size(x_2);
lean_inc_ref(x_2);
x_37 = l_Array_toSubarray___redArg(x_2, x_28, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_size(x_35);
x_45 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_46 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(x_38, x_5, x_6, x_35, x_44, x_45, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_35);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_48, 1);
x_50 = lean_ctor_get(x_49, 1);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_46);
x_71 = lean_ctor_get(x_54, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_dec(x_54);
x_73 = l_Lean_Expr_cleanupAnnotations(x_72);
x_74 = l_Lean_Expr_isApp(x_73);
if (x_74 == 0)
{
lean_dec_ref(x_73);
lean_dec(x_71);
lean_dec(x_53);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_75);
x_76 = l_Lean_Expr_appFnCleanup___redArg(x_73);
x_77 = l_Lean_Expr_isApp(x_76);
if (x_77 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec(x_71);
lean_dec(x_53);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_76);
x_79 = l_Lean_Expr_isApp(x_78);
if (x_79 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_75);
lean_dec(x_71);
lean_dec(x_53);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_81 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
lean_dec_ref(x_80);
if (x_82 == 0)
{
lean_dec_ref(x_75);
lean_dec(x_71);
lean_dec(x_53);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_83 = lean_expr_instantiate_rev(x_75, x_71);
lean_dec(x_71);
lean_dec_ref(x_75);
x_84 = lean_nat_dec_lt(x_28, x_36);
if (x_84 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_55 = x_83;
x_56 = x_10;
x_57 = lean_box(0);
goto block_70;
}
else
{
if (x_84 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_55 = x_83;
x_56 = x_10;
x_57 = lean_box(0);
goto block_70;
}
else
{
size_t x_85; uint8_t x_86; 
x_85 = lean_usize_of_nat(x_36);
x_86 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_82, x_2, x_45, x_85);
lean_dec_ref(x_2);
if (x_86 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_55 = x_83;
x_56 = x_10;
x_57 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_87; 
x_87 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_83, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_55 = x_88;
x_56 = x_10;
x_57 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_89; 
lean_dec(x_53);
lean_dec(x_10);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
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
else
{
lean_object* x_92; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_92 = lean_ctor_get(x_52, 0);
lean_inc(x_92);
lean_dec_ref(x_52);
lean_ctor_set(x_46, 0, x_92);
return x_46;
}
block_70:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_55, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = 0;
x_62 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_61);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = 0;
x_65 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_53);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_53);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
return x_58;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_93 = lean_ctor_get(x_46, 0);
lean_inc(x_93);
lean_dec(x_46);
x_94 = lean_ctor_get(x_93, 1);
x_95 = lean_ctor_get(x_94, 1);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_99, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = l_Lean_Expr_cleanupAnnotations(x_114);
x_116 = l_Lean_Expr_isApp(x_115);
if (x_116 == 0)
{
lean_dec_ref(x_115);
lean_dec(x_113);
lean_dec(x_98);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_117);
x_118 = l_Lean_Expr_appFnCleanup___redArg(x_115);
x_119 = l_Lean_Expr_isApp(x_118);
if (x_119 == 0)
{
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_113);
lean_dec(x_98);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_Expr_appFnCleanup___redArg(x_118);
x_121 = l_Lean_Expr_isApp(x_120);
if (x_121 == 0)
{
lean_dec_ref(x_120);
lean_dec_ref(x_117);
lean_dec(x_113);
lean_dec(x_98);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = l_Lean_Expr_appFnCleanup___redArg(x_120);
x_123 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4;
x_124 = l_Lean_Expr_isConstOf(x_122, x_123);
lean_dec_ref(x_122);
if (x_124 == 0)
{
lean_dec_ref(x_117);
lean_dec(x_113);
lean_dec(x_98);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_125 = lean_expr_instantiate_rev(x_117, x_113);
lean_dec(x_113);
lean_dec_ref(x_117);
x_126 = lean_nat_dec_lt(x_28, x_36);
if (x_126 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_100 = x_125;
x_101 = x_10;
x_102 = lean_box(0);
goto block_112;
}
else
{
if (x_126 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_100 = x_125;
x_101 = x_10;
x_102 = lean_box(0);
goto block_112;
}
else
{
size_t x_127; uint8_t x_128; 
x_127 = lean_usize_of_nat(x_36);
x_128 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(x_124, x_2, x_45, x_127);
lean_dec_ref(x_2);
if (x_128 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_100 = x_125;
x_101 = x_10;
x_102 = lean_box(0);
goto block_112;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_125, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_100 = x_130;
x_101 = x_10;
x_102 = lean_box(0);
goto block_112;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_98);
lean_dec(x_10);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
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
lean_object* x_134; lean_object* x_135; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_134 = lean_ctor_get(x_97, 0);
lean_inc(x_134);
lean_dec_ref(x_97);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
block_112:
{
lean_object* x_103; 
x_103 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_100, x_101);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = 0;
x_107 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_98);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_106);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 1, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
return x_111;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_136 = !lean_is_exclusive(x_46);
if (x_136 == 0)
{
return x_46;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_46, 0);
lean_inc(x_137);
lean_dec(x_46);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0;
x_26 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_25, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_2, x_3, x_4, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
lean_inc_ref(x_14);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed), 15, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_13);
lean_closure_set(x_16, 4, x_15);
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
x_18 = lean_array_get_size(x_14);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
x_25 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(x_14, x_16, x_1, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_16);
lean_dec_ref(x_14);
x_26 = lean_box(x_19);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed), 11, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_27, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed), 13, 3);
lean_closure_set(x_29, 0, x_18);
lean_closure_set(x_29, 1, x_14);
lean_closure_set(x_29, 2, x_16);
x_30 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_31 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(x_29, x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_12 = l_Lean_Meta_Sym_getCongrInfo(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_12);
x_19 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_14);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_12);
x_21 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_14);
x_22 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec_ref(x_23);
x_28 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix(x_1, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_26);
return x_28;
}
case 2:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_23);
x_30 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_23);
x_32 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_Simp_simpAppArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.simpAppArgRange.visit", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(470u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(478u);
x_4 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_3, x_21);
x_23 = lean_nat_dec_lt(x_22, x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_19);
x_24 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_1, x_19, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
if (x_23 == 0)
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
x_28 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_19, x_20, x_26, x_27, x_14, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_19);
x_30 = l_Lean_Meta_Sym_inferType(x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_32 = l_Lean_Meta_whnfD(x_31, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; uint8_t x_48; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_35);
lean_dec_ref(x_33);
x_48 = l_Lean_Expr_hasLooseBVars(x_35);
lean_dec_ref(x_35);
if (x_48 == 0)
{
goto block_47;
}
else
{
if (x_14 == 0)
{
lean_dec_ref(x_34);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_29);
x_51 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_2, x_19, x_20, x_49, x_50, x_14, x_7, x_8, x_9, x_10, x_11);
return x_51;
}
}
else
{
goto block_47;
}
}
block_47:
{
lean_object* x_36; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_36 = l_Lean_Meta_isProp(x_34, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_20);
x_39 = lean_sym_simp(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_19, x_20, x_29, x_40, x_7, x_8, x_9, x_10, x_11);
return x_41;
}
else
{
lean_dec(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_39;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_42 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_42, 0, x_14);
x_43 = l_Lean_Meta_Sym_Simp_mkCongr___redArg(x_2, x_19, x_20, x_29, x_42, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_2);
x_52 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1;
x_53 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_32);
if (x_54 == 0)
{
return x_32;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_32, 0);
lean_inc(x_55);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_29);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_30);
if (x_57 == 0)
{
return x_30;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_2);
x_60 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2;
x_61 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_62 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.simpAppArgRange", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: start < stop\n  ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(454u);
x_4 = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2;
x_15 = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_getAppNumArgs(x_1);
x_17 = lean_nat_dec_lt(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_nat_sub(x_16, x_2);
lean_dec(x_16);
x_19 = lean_nat_sub(x_3, x_2);
x_20 = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(x_19, x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_21 = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5);
l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6 = _init_l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__2);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__3);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0 = _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0);
l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1 = _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1);
l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2 = _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
