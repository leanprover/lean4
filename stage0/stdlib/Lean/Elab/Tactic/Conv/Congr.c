// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Congr
// Imports: public import Lean.Meta.Tactic.Simp.Main public import Lean.Meta.Tactic.Congr public import Lean.Elab.Tactic.Conv.Basic
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
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0;
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3;
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6;
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__3;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9;
static lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3;
lean_object* l_Subarray_toArray___redArg(lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static uint64_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__2;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__4;
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5;
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2;
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1;
static lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object**);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSkip(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Conv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSkip", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSkip___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(95u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(88u);
x_2 = lean_unsigned_to_nat(95u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(88u);
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(47u);
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(95u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = lean_unsigned_to_nat(95u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(51u);
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implies_congr", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'apply implies_congr' unexpected result", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1;
lean_inc_ref(x_4);
x_8 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2;
x_11 = lean_box(0);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_MVarId_apply(x_1, x_9, x_10, x_11, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 1)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
if (lean_obj_tag(x_24) == 1)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec_ref(x_13);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec_ref(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_31 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_29, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_30, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_24, 0, x_35);
lean_ctor_set(x_22, 0, x_32);
lean_ctor_set(x_33, 0, x_22);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_24, 0, x_36);
lean_ctor_set(x_22, 0, x_32);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_22);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_32);
lean_free_object(x_24);
lean_free_object(x_22);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_30);
lean_free_object(x_24);
lean_free_object(x_22);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_free_object(x_24);
lean_dec(x_27);
lean_free_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec_ref(x_13);
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec_ref(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_47 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_45, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_46, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_22, 1, x_52);
lean_ctor_set(x_22, 0, x_48);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_22);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
lean_free_object(x_22);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_46);
lean_free_object(x_22);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_58 = x_47;
} else {
 lean_dec_ref(x_47);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
else
{
lean_dec(x_44);
lean_free_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
}
else
{
lean_free_object(x_22);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_dec(x_22);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; 
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
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
lean_dec_ref(x_13);
x_64 = lean_ctor_get(x_21, 0);
lean_inc(x_64);
lean_dec_ref(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_65 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_63, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_64, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_62;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_61);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_66);
lean_dec(x_62);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_77 = x_65;
} else {
 lean_dec_ref(x_65);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
else
{
lean_dec(x_60);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
}
else
{
lean_dec(x_13);
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
goto block_20;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4;
x_19 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_18, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
return x_19;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
uint8_t x_79; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_8);
if (x_79 == 0)
{
return x_8;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_8, 0);
lean_inc(x_80);
lean_dec(x_8);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isArrow(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = l_Lean_Meta_isProp(x_10, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_11);
x_14 = l_Lean_Expr_bindingBody_x21(x_1);
x_15 = l_Lean_Meta_isProp(x_14, x_2, x_3, x_4, x_5);
return x_15;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Expr_app___override(x_3, x_16);
lean_inc(x_17);
x_19 = l_Lean_mkApp3(x_5, x_1, x_16, x_17);
x_20 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_array_push(x_4, x_21);
lean_ctor_set(x_14, 1, x_19);
lean_ctor_set(x_14, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
lean_inc(x_26);
x_28 = l_Lean_Expr_app___override(x_3, x_26);
lean_inc(x_27);
x_29 = l_Lean_mkApp3(x_5, x_1, x_26, x_27);
x_30 = l_Lean_Expr_mvarId_x21(x_27);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_push(x_4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
lean_dec(x_12);
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
lean_inc(x_38);
x_41 = l_Lean_Expr_app___override(x_3, x_38);
lean_inc(x_39);
x_42 = l_Lean_mkApp3(x_5, x_1, x_38, x_39);
x_43 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_push(x_4, x_44);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Conv.Congr", 27, 27);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Tactic.Conv.Congr.0.Lean.Elab.Tactic.Conv.mkCongrThm", 71, 71);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_unsigned_to_nat(68u);
x_4 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1;
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3;
x_12 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_36; 
x_36 = lean_nat_dec_lt(x_10, x_1);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_11);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_41 = x_11;
} else {
 lean_dec_ref(x_11);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_2);
x_48 = lean_array_get_borrowed(x_2, x_3, x_10);
lean_inc_ref(x_7);
x_49 = lean_array_get_borrowed(x_7, x_47, x_10);
x_50 = lean_array_fget_borrowed(x_8, x_10);
x_51 = lean_unbox(x_50);
switch (x_51) {
case 1:
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
x_52 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_53 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(x_44, x_45, x_42, x_40, x_52, x_12, x_13, x_14, x_15);
x_23 = x_53;
goto block_35;
}
case 2:
{
if (x_9 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Meta_ParamInfo_isExplicit(x_49);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_inc(x_48);
x_70 = l_Lean_Expr_app___override(x_40, x_48);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_48);
x_71 = l_Lean_Meta_mkEqRefl(x_48, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc_n(x_48, 2);
x_73 = l_Lean_mkApp3(x_45, x_48, x_48, x_72);
if (lean_is_scalar(x_46)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_46;
}
lean_ctor_set(x_74, 0, x_44);
lean_ctor_set(x_74, 1, x_73);
if (lean_is_scalar(x_43)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_43;
}
lean_ctor_set(x_75, 0, x_42);
lean_ctor_set(x_75, 1, x_74);
if (lean_is_scalar(x_41)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_41;
}
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
x_17 = x_76;
x_18 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_77; 
lean_dec_ref(x_70);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
goto block_68;
}
}
else
{
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
goto block_68;
}
block_68:
{
if (x_4 == 0)
{
lean_object* x_54; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_5);
lean_inc(x_48);
x_54 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(x_48, x_44, x_40, x_42, x_45, x_5, x_12, x_13, x_14, x_15);
x_23 = x_54;
goto block_35;
}
else
{
lean_object* x_55; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_45);
x_55 = lean_infer_type(x_45, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_57 = lean_whnf(x_56, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Expr_bindingName_x21(x_58);
lean_dec(x_58);
lean_inc(x_5);
x_60 = l_Lean_Meta_appendTag(x_5, x_59);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_48);
x_61 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(x_48, x_44, x_40, x_42, x_45, x_60, x_12, x_13, x_14, x_15);
x_23 = x_61;
goto block_35;
}
else
{
uint8_t x_62; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
lean_dec(x_55);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
}
case 4:
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
x_80 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_81 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(x_44, x_45, x_42, x_40, x_80, x_12, x_13, x_14, x_15);
x_23 = x_81;
goto block_35;
}
case 5:
{
lean_object* x_82; lean_object* x_83; 
lean_inc(x_48);
x_82 = l_Lean_Expr_app___override(x_45, x_48);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_82);
x_83 = lean_infer_type(x_82, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_85 = lean_whnf(x_84, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lean_Expr_bindingDomain_x21(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = 0;
x_90 = lean_box(0);
lean_inc_ref(x_12);
x_91 = l_Lean_Meta_mkFreshExprMVar(x_88, x_89, x_90, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_92);
x_93 = l_Lean_Expr_app___override(x_40, x_92);
lean_inc(x_92);
x_94 = l_Lean_Expr_app___override(x_82, x_92);
x_95 = l_Lean_Expr_mvarId_x21(x_92);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_array_push(x_44, x_96);
if (lean_is_scalar(x_46)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_46;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
if (lean_is_scalar(x_43)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_43;
}
lean_ctor_set(x_99, 0, x_42);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_41)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_41;
}
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_99);
x_17 = x_100;
x_18 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_101; 
lean_dec_ref(x_82);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_101 = !lean_is_exclusive(x_91);
if (x_101 == 0)
{
return x_91;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
lean_dec(x_91);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_82);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_104 = !lean_is_exclusive(x_85);
if (x_104 == 0)
{
return x_85;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_85, 0);
lean_inc(x_105);
lean_dec(x_85);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec_ref(x_82);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_107 = !lean_is_exclusive(x_83);
if (x_107 == 0)
{
return x_83;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_83, 0);
lean_inc(x_108);
lean_dec(x_83);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
default: 
{
lean_object* x_110; lean_object* x_111; 
lean_inc(x_48);
x_110 = l_Lean_Expr_app___override(x_40, x_48);
lean_inc(x_48);
x_111 = l_Lean_Expr_app___override(x_45, x_48);
if (x_9 == 0)
{
uint8_t x_118; 
x_118 = l_Lean_Meta_ParamInfo_isExplicit(x_49);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_44);
lean_ctor_set(x_119, 1, x_111);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_42);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_110);
lean_ctor_set(x_121, 1, x_120);
x_17 = x_121;
x_18 = lean_box(0);
goto block_22;
}
else
{
goto block_117;
}
}
else
{
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = lean_array_push(x_42, x_112);
if (lean_is_scalar(x_46)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_46;
}
lean_ctor_set(x_114, 0, x_44);
lean_ctor_set(x_114, 1, x_111);
if (lean_is_scalar(x_43)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_43;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_41)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_41;
}
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
x_17 = x_116;
x_18 = lean_box(0);
goto block_22;
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_10, x_19);
lean_dec(x_10);
x_10 = x_20;
x_11 = x_17;
goto _start;
}
block_35:
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; 
lean_free_object(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec_ref(x_25);
x_17 = x_27;
x_18 = lean_box(0);
goto block_22;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_17 = x_31;
x_18 = lean_box(0);
goto block_22;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_9);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_14);
x_15 = l_Lean_Meta_mkCongrFun(x_2, x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_10, x_17);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_18);
x_2 = x_16;
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget_borrowed(x_20, x_21);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_25);
x_26 = l_Lean_Meta_mkCongrFun(x_2, x_25, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_22);
x_1 = x_30;
x_2 = x_27;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'congr' conv tactic failed to create congruence theorem", 55, 55);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_get_size(x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_20 = l_Lean_Meta_getFunInfoNArgs(x_2, x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_22 = l_Lean_Meta_getCongrSimpKinds(x_2, x_21, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_21);
lean_inc_ref(x_2);
x_25 = l_Lean_Meta_mkCongrSimpCore_x3f(x_2, x_21, x_23, x_24, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = l_Lean_instInhabitedExpr;
x_31 = l_Lean_Meta_instInhabitedParamInfo_default;
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0;
x_34 = lean_array_get_size(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_28);
x_36 = lean_nat_dec_lt(x_34, x_19);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_39 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(x_34, x_30, x_3, x_5, x_1, x_21, x_31, x_29, x_4, x_32, x_38, x_6, x_7, x_8, x_9);
lean_dec_ref(x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_85; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
if (x_36 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
x_86 = lean_ctor_get(x_42, 0);
lean_inc(x_86);
lean_dec(x_42);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_11 = x_86;
x_12 = x_87;
x_13 = x_88;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_42, 0);
lean_inc(x_89);
lean_dec(x_42);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_nat_dec_eq(x_34, x_32);
if (x_92 == 0)
{
x_74 = x_89;
x_75 = x_90;
x_76 = x_91;
x_77 = x_6;
x_78 = x_7;
x_79 = x_8;
x_80 = x_9;
x_81 = lean_box(0);
goto block_84;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2;
x_94 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_93, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_74 = x_89;
x_75 = x_90;
x_76 = x_91;
x_77 = x_6;
x_78 = x_7;
x_79 = x_8;
x_80 = x_9;
x_81 = lean_box(0);
goto block_84;
}
else
{
uint8_t x_95; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
block_73:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Array_toSubarray___redArg(x_3, x_51, x_52);
lean_inc_ref(x_53);
x_54 = l_Subarray_toArray___redArg(x_53);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_43);
lean_inc_ref(x_46);
x_55 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(x_1, x_41, x_54, x_4, x_5, x_46, x_43, x_49, x_50);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_43);
lean_inc_ref(x_46);
x_61 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(x_53, x_44, x_46, x_43, x_49, x_50);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_mkEqTrans(x_62, x_58, x_46, x_43, x_49, x_50);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Array_append___redArg(x_48, x_59);
lean_dec(x_59);
x_66 = l_Array_append___redArg(x_47, x_60);
lean_dec(x_60);
x_11 = x_65;
x_12 = x_66;
x_13 = x_64;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_67; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
x_70 = !lean_is_exclusive(x_61);
if (x_70 == 0)
{
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
lean_dec(x_61);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_dec_ref(x_53);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_44);
lean_dec(x_43);
return x_55;
}
}
block_84:
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Meta_FunInfo_getArity(x_21);
lean_dec(x_21);
x_83 = lean_nat_dec_le(x_82, x_32);
if (x_83 == 0)
{
x_43 = x_78;
x_44 = x_76;
x_45 = lean_box(0);
x_46 = x_77;
x_47 = x_75;
x_48 = x_74;
x_49 = x_79;
x_50 = x_80;
x_51 = x_82;
x_52 = x_19;
goto block_73;
}
else
{
lean_dec(x_82);
x_43 = x_78;
x_44 = x_76;
x_45 = lean_box(0);
x_46 = x_77;
x_47 = x_75;
x_48 = x_74;
x_49 = x_79;
x_50 = x_80;
x_51 = x_32;
x_52 = x_19;
goto block_73;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_39);
if (x_98 == 0)
{
return x_39;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
lean_dec(x_39);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_101 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2;
x_102 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_101, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_25);
if (x_103 == 0)
{
return x_25;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_25, 0);
lean_inc(x_104);
lean_dec(x_25);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_22);
if (x_106 == 0)
{
return x_22;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_22, 0);
lean_inc(x_107);
lean_dec(x_22);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_20);
if (x_109 == 0)
{
return x_20;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_20, 0);
lean_inc(x_110);
lean_dec(x_20);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; 
x_20 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_15, x_16, x_17, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_4);
x_21 = lean_unbox(x_9);
x_22 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid `", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic, failed to resolve", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n=\?=", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_9 = l_Lean_Meta_isExprDefEqGuarded(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_9);
x_13 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_14 = l_Lean_stringToMessageData(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_2);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_3);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_23, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_29 = l_Lean_stringToMessageData(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_2);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_3);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_38, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic failed, equality expected", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = lean_whnf(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1;
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity(x_12, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec_ref(x_2);
x_16 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
x_17 = l_Lean_stringToMessageData(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_20, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_23 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_1, x_2, x_22, x_4, x_5, x_6, x_7);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_instBEqMVarId_beq(x_3, x_12);
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
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_instBEqMVarId_beq(x_3, x_26);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
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
x_25 = l_Lean_instBEqMVarId_beq(x_4, x_23);
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
x_30 = l_Lean_instBEqMVarId_beq(x_4, x_28);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_35, x_36, x_37, x_4, x_5);
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
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_39, x_40, x_41, x_4, x_5);
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
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(x_1, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(x_3, x_48, x_49, x_50, x_51);
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
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(x_61, x_4, x_5);
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
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(x_3, x_64, x_65, x_66, x_67);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_9, x_1, x_2);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_23 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_21, x_1, x_2);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_40, x_1, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 9, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_43);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_31);
lean_ctor_set(x_45, 4, x_32);
x_46 = lean_st_ref_set(x_3, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'congr' conv tactic, application or implication expected", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_11 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_14, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_19 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(x_18, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isApp(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_1);
x_23 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1;
x_24 = l_Lean_indentExpr(x_18);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_23);
x_25 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_12, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_12);
x_26 = l_Lean_Expr_getAppFn(x_18);
x_27 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
x_28 = l_Lean_Expr_getAppNumArgs(x_18);
lean_inc(x_28);
x_29 = lean_mk_array(x_28, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_18, x_29, x_31);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_33 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(x_10, x_26, x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3;
lean_inc(x_5);
lean_inc(x_36);
x_40 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_39, x_15, x_36, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec_ref(x_40);
x_41 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_36, x_5);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_array_to_list(x_37);
x_45 = lean_array_to_list(x_38);
x_46 = l_List_appendTR___redArg(x_44, x_45);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
x_47 = lean_array_to_list(x_37);
x_48 = lean_array_to_list(x_38);
x_49 = l_List_appendTR___redArg(x_47, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_33);
if (x_54 == 0)
{
return x_33;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_33, 0);
lean_inc(x_55);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; 
lean_dec_ref(x_18);
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_10);
x_57 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_box(0);
x_61 = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(x_59, x_60);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_box(0);
x_64 = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(x_62, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_57);
if (x_66 == 0)
{
return x_57;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_57, 0);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_18);
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_19, 0);
lean_inc(x_70);
lean_dec(x_19);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_12, 0);
x_73 = lean_ctor_get(x_12, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_12);
x_74 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_72, x_5);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Expr_cleanupAnnotations(x_75);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_77 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(x_76, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_isApp(x_76);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_73);
lean_dec(x_10);
lean_dec(x_1);
x_81 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1;
x_82 = l_Lean_indentExpr(x_76);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_83, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = l_Lean_Expr_getAppFn(x_76);
x_86 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
x_87 = l_Lean_Expr_getAppNumArgs(x_76);
lean_inc(x_87);
x_88 = lean_mk_array(x_87, x_86);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_87, x_89);
lean_dec(x_87);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_76, x_88, x_90);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_92 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(x_10, x_85, x_91, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3;
lean_inc(x_5);
lean_inc(x_95);
x_99 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_98, x_73, x_95, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_99);
x_100 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_95, x_5);
lean_dec(x_5);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_101 = x_100;
} else {
 lean_dec_ref(x_100);
 x_101 = lean_box(0);
}
x_102 = lean_array_to_list(x_96);
x_103 = lean_array_to_list(x_97);
x_104 = l_List_appendTR___redArg(x_102, x_103);
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_101;
}
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_1);
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_109 = lean_ctor_get(x_92, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_110 = x_92;
} else {
 lean_dec_ref(x_92);
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
else
{
lean_object* x_112; 
lean_dec_ref(x_76);
lean_dec(x_73);
lean_dec(x_10);
x_112 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
x_116 = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(x_113, x_115);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_76);
lean_dec(x_73);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_77, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_122 = x_77;
} else {
 lean_dec_ref(x_77);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_11);
if (x_124 == 0)
{
return x_11;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_11, 0);
lean_inc(x_125);
lean_dec(x_11);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_9);
if (x_127 == 0)
{
return x_9;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_9, 0);
lean_inc(x_128);
lean_dec(x_9);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Elab_Tactic_Conv_congr___lam__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(x_2);
x_10 = lean_box(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_1, x_11, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Elab_Tactic_Conv_congr(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = 0;
x_10 = 1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = l_Lean_Elab_Tactic_Conv_congr(x_8, x_9, x_10, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0;
x_14 = l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(x_12, x_13);
x_15 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_14, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalCongr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0;
x_4 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCongr___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(52u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(61u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(61u);
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(52u);
x_4 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_Meta_mkCongrFun(x_4, x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
else
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg 0", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_18 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_3, x_17, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_37; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_4);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_inc(x_21);
x_22 = x_21;
x_23 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
if (x_45 == 0)
{
lean_inc(x_21);
x_22 = x_21;
x_23 = lean_box(0);
goto block_36;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_21);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(x_4, x_47, x_48, x_21, x_6, x_7, x_8, x_9);
x_37 = x_49;
goto block_42;
}
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_21);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(x_4, x_50, x_51, x_21, x_6, x_7, x_8, x_9);
x_37 = x_52;
goto block_42;
}
}
block_36:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_22, x_7);
lean_dec_ref(x_24);
x_25 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0;
x_26 = l_Lean_mkAppN(x_20, x_4);
lean_dec_ref(x_4);
x_27 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_25, x_2, x_26, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
x_31 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
block_42:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_22 = x_38;
x_23 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
return x_18;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_18, 0);
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'arg 0' conv tactic, application expected", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_27; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_10, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Expr_cleanupAnnotations(x_13);
x_27 = l_Lean_Expr_isApp(x_14);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_1);
x_28 = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1;
x_29 = l_Lean_indentExpr(x_14);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_8, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_free_object(x_8);
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
x_21 = l_Lean_Expr_getAppNumArgs(x_14);
lean_inc(x_21);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_21, x_23);
lean_dec(x_21);
x_25 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(x_1, x_11, x_14, x_22, x_24, x_15, x_16, x_17, x_18);
return x_25;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_51; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_34, x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_Expr_cleanupAnnotations(x_37);
x_51 = l_Lean_Expr_isApp(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_35);
lean_dec(x_1);
x_52 = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1;
x_53 = l_Lean_indentExpr(x_38);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_54, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
x_39 = x_2;
x_40 = x_3;
x_41 = x_4;
x_42 = x_5;
x_43 = lean_box(0);
goto block_50;
}
block_50:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
x_45 = l_Lean_Expr_getAppNumArgs(x_38);
lean_inc(x_45);
x_46 = lean_mk_array(x_45, x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_45, x_47);
lean_dec(x_45);
x_49 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(x_1, x_35, x_38, x_46, x_48, x_39, x_40, x_41, x_42);
return x_49;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
return x_7;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
lean_dec(x_7);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Conv_congrFunN(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_14);
x_15 = l_Lean_Meta_mkCongrFun(x_2, x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_10, x_17);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_18);
x_2 = x_16;
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget_borrowed(x_20, x_21);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_25);
x_26 = l_Lean_Meta_mkCongrFun(x_2, x_25, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_22);
x_1 = x_30;
x_2 = x_27;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Expr_mvarId_x21(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Tactic.Conv.Congr.0.Lean.Elab.Tactic.Conv.mkCongrArgZeroThm", 78, 78);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_unsigned_to_nat(150u);
x_4 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0;
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1;
x_12 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic failed, cannot select argument", 44, 44);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_7, x_1);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_2);
x_46 = lean_array_get_borrowed(x_2, x_3, x_7);
x_47 = lean_array_fget_borrowed(x_4, x_7);
x_48 = lean_unbox(x_47);
switch (x_48) {
case 1:
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_8);
x_49 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_50 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_44, x_45, x_41, x_38, x_49, x_9, x_10, x_11, x_12);
x_20 = x_50;
goto block_32;
}
case 2:
{
lean_object* x_51; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_8);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_5);
lean_inc(x_46);
x_51 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_46, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_56 = l_Lean_Expr_app___override(x_38, x_54);
lean_inc(x_55);
lean_inc(x_46);
x_57 = l_Lean_mkApp3(x_45, x_46, x_54, x_55);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_52);
x_58 = lean_box(0);
x_59 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_55, x_44, x_57, x_56, x_41, x_58, x_9, x_10, x_11, x_12);
lean_dec(x_55);
x_20 = x_59;
goto block_32;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
lean_inc_ref(x_6);
x_61 = l_Lean_stringToMessageData(x_6);
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_60);
x_62 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_63, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_55, x_44, x_57, x_56, x_41, x_65, x_9, x_10, x_11, x_12);
lean_dec_ref(x_41);
lean_dec(x_55);
x_20 = x_66;
goto block_32;
}
else
{
uint8_t x_67; 
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_44);
lean_dec_ref(x_41);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
lean_inc(x_70);
x_72 = l_Lean_Expr_app___override(x_38, x_70);
lean_inc(x_71);
lean_inc(x_46);
x_73 = l_Lean_mkApp3(x_45, x_46, x_70, x_71);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_box(0);
x_75 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_71, x_44, x_73, x_72, x_41, x_74, x_9, x_10, x_11, x_12);
lean_dec(x_71);
x_20 = x_75;
goto block_32;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
lean_inc_ref(x_6);
x_77 = l_Lean_stringToMessageData(x_6);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_80, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_71, x_44, x_73, x_72, x_41, x_82, x_9, x_10, x_11, x_12);
lean_dec_ref(x_41);
lean_dec(x_71);
x_20 = x_83;
goto block_32;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_44);
lean_dec_ref(x_41);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_51);
if (x_87 == 0)
{
return x_51;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_51, 0);
lean_inc(x_88);
lean_dec(x_51);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
case 4:
{
lean_object* x_90; lean_object* x_91; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_8);
x_90 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_91 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_44, x_45, x_41, x_38, x_90, x_9, x_10, x_11, x_12);
x_20 = x_91;
goto block_32;
}
case 5:
{
lean_object* x_92; lean_object* x_93; 
lean_inc(x_46);
x_92 = l_Lean_Expr_app___override(x_45, x_46);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_92);
x_93 = lean_infer_type(x_92, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_95 = lean_whnf(x_94, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_Expr_bindingDomain_x21(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = 0;
x_100 = lean_box(0);
lean_inc_ref(x_9);
x_101 = l_Lean_Meta_mkFreshExprMVar(x_98, x_99, x_100, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
lean_inc(x_102);
x_103 = l_Lean_Expr_app___override(x_38, x_102);
lean_inc(x_102);
x_104 = l_Lean_Expr_app___override(x_92, x_102);
x_105 = l_Lean_Expr_mvarId_x21(x_102);
lean_dec(x_102);
x_106 = lean_array_push(x_44, x_105);
lean_ctor_set(x_36, 1, x_104);
lean_ctor_set(x_36, 0, x_106);
lean_ctor_set(x_8, 0, x_103);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_107; 
lean_dec_ref(x_92);
lean_free_object(x_36);
lean_dec(x_44);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_107 = !lean_is_exclusive(x_101);
if (x_107 == 0)
{
return x_101;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec_ref(x_92);
lean_free_object(x_36);
lean_dec(x_44);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_95);
if (x_110 == 0)
{
return x_95;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_95, 0);
lean_inc(x_111);
lean_dec(x_95);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec_ref(x_92);
lean_free_object(x_36);
lean_dec(x_44);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_113 = !lean_is_exclusive(x_93);
if (x_113 == 0)
{
return x_93;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_93, 0);
lean_inc(x_114);
lean_dec(x_93);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
default: 
{
lean_object* x_116; lean_object* x_117; 
lean_inc(x_46);
x_116 = l_Lean_Expr_app___override(x_38, x_46);
lean_inc(x_46);
x_117 = l_Lean_Expr_app___override(x_45, x_46);
lean_ctor_set(x_36, 1, x_117);
lean_ctor_set(x_8, 0, x_116);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_36, 0);
x_119 = lean_ctor_get(x_36, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_36);
lean_inc_ref(x_2);
x_120 = lean_array_get_borrowed(x_2, x_3, x_7);
x_121 = lean_array_fget_borrowed(x_4, x_7);
x_122 = lean_unbox(x_121);
switch (x_122) {
case 1:
{
lean_object* x_123; lean_object* x_124; 
lean_free_object(x_35);
lean_free_object(x_8);
x_123 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_124 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_118, x_119, x_41, x_38, x_123, x_9, x_10, x_11, x_12);
x_20 = x_124;
goto block_32;
}
case 2:
{
lean_object* x_125; 
lean_free_object(x_35);
lean_free_object(x_8);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_5);
lean_inc(x_120);
x_125 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_120, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
lean_inc(x_127);
x_130 = l_Lean_Expr_app___override(x_38, x_127);
lean_inc(x_128);
lean_inc(x_120);
x_131 = l_Lean_mkApp3(x_119, x_120, x_127, x_128);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_129);
x_132 = lean_box(0);
x_133 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_128, x_118, x_131, x_130, x_41, x_132, x_9, x_10, x_11, x_12);
lean_dec(x_128);
x_20 = x_133;
goto block_32;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
lean_inc_ref(x_6);
x_135 = l_Lean_stringToMessageData(x_6);
if (lean_is_scalar(x_129)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_129;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_138, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_128, x_118, x_131, x_130, x_41, x_140, x_9, x_10, x_11, x_12);
lean_dec_ref(x_41);
lean_dec(x_128);
x_20 = x_141;
goto block_32;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_128);
lean_dec(x_118);
lean_dec_ref(x_41);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_145 = lean_ctor_get(x_125, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_146 = x_125;
} else {
 lean_dec_ref(x_125);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
case 4:
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_35);
lean_free_object(x_8);
x_148 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_149 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_118, x_119, x_41, x_38, x_148, x_9, x_10, x_11, x_12);
x_20 = x_149;
goto block_32;
}
case 5:
{
lean_object* x_150; lean_object* x_151; 
lean_inc(x_120);
x_150 = l_Lean_Expr_app___override(x_119, x_120);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_150);
x_151 = lean_infer_type(x_150, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_153 = lean_whnf(x_152, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = l_Lean_Expr_bindingDomain_x21(x_154);
lean_dec(x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = 0;
x_158 = lean_box(0);
lean_inc_ref(x_9);
x_159 = l_Lean_Meta_mkFreshExprMVar(x_156, x_157, x_158, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
lean_inc(x_160);
x_161 = l_Lean_Expr_app___override(x_38, x_160);
lean_inc(x_160);
x_162 = l_Lean_Expr_app___override(x_150, x_160);
x_163 = l_Lean_Expr_mvarId_x21(x_160);
lean_dec(x_160);
x_164 = lean_array_push(x_118, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
lean_ctor_set(x_35, 1, x_165);
lean_ctor_set(x_8, 0, x_161);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_150);
lean_dec(x_118);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_166 = lean_ctor_get(x_159, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_167 = x_159;
} else {
 lean_dec_ref(x_159);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_150);
lean_dec(x_118);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_169 = lean_ctor_get(x_153, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_170 = x_153;
} else {
 lean_dec_ref(x_153);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_150);
lean_dec(x_118);
lean_free_object(x_35);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_172 = lean_ctor_get(x_151, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_173 = x_151;
} else {
 lean_dec_ref(x_151);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_inc(x_120);
x_175 = l_Lean_Expr_app___override(x_38, x_120);
lean_inc(x_120);
x_176 = l_Lean_Expr_app___override(x_119, x_120);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_118);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_35, 1, x_177);
lean_ctor_set(x_8, 0, x_175);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_178 = lean_ctor_get(x_35, 0);
lean_inc(x_178);
lean_dec(x_35);
x_179 = lean_ctor_get(x_36, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_36, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_181 = x_36;
} else {
 lean_dec_ref(x_36);
 x_181 = lean_box(0);
}
lean_inc_ref(x_2);
x_182 = lean_array_get_borrowed(x_2, x_3, x_7);
x_183 = lean_array_fget_borrowed(x_4, x_7);
x_184 = lean_unbox(x_183);
switch (x_184) {
case 1:
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_181);
lean_free_object(x_8);
x_185 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_186 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_179, x_180, x_178, x_38, x_185, x_9, x_10, x_11, x_12);
x_20 = x_186;
goto block_32;
}
case 2:
{
lean_object* x_187; 
lean_dec(x_181);
lean_free_object(x_8);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_5);
lean_inc(x_182);
x_187 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_182, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
lean_inc(x_189);
x_192 = l_Lean_Expr_app___override(x_38, x_189);
lean_inc(x_190);
lean_inc(x_182);
x_193 = l_Lean_mkApp3(x_180, x_182, x_189, x_190);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_191);
x_194 = lean_box(0);
x_195 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_190, x_179, x_193, x_192, x_178, x_194, x_9, x_10, x_11, x_12);
lean_dec(x_190);
x_20 = x_195;
goto block_32;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
lean_inc_ref(x_6);
x_197 = l_Lean_stringToMessageData(x_6);
if (lean_is_scalar(x_191)) {
 x_198 = lean_alloc_ctor(7, 2, 0);
} else {
 x_198 = x_191;
 lean_ctor_set_tag(x_198, 7);
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_200, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_190, x_179, x_193, x_192, x_178, x_202, x_9, x_10, x_11, x_12);
lean_dec_ref(x_178);
lean_dec(x_190);
x_20 = x_203;
goto block_32;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_190);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_207 = lean_ctor_get(x_187, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_208 = x_187;
} else {
 lean_dec_ref(x_187);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
}
case 4:
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_181);
lean_free_object(x_8);
x_210 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_211 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_179, x_180, x_178, x_38, x_210, x_9, x_10, x_11, x_12);
x_20 = x_211;
goto block_32;
}
case 5:
{
lean_object* x_212; lean_object* x_213; 
lean_inc(x_182);
x_212 = l_Lean_Expr_app___override(x_180, x_182);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_212);
x_213 = lean_infer_type(x_212, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_215 = lean_whnf(x_214, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l_Lean_Expr_bindingDomain_x21(x_216);
lean_dec(x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = 0;
x_220 = lean_box(0);
lean_inc_ref(x_9);
x_221 = l_Lean_Meta_mkFreshExprMVar(x_218, x_219, x_220, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
lean_inc(x_222);
x_223 = l_Lean_Expr_app___override(x_38, x_222);
lean_inc(x_222);
x_224 = l_Lean_Expr_app___override(x_212, x_222);
x_225 = l_Lean_Expr_mvarId_x21(x_222);
lean_dec(x_222);
x_226 = lean_array_push(x_179, x_225);
if (lean_is_scalar(x_181)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_181;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_178);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_8, 1, x_228);
lean_ctor_set(x_8, 0, x_223);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec_ref(x_212);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_229 = lean_ctor_get(x_221, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_230 = x_221;
} else {
 lean_dec_ref(x_221);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_212);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_232 = lean_ctor_get(x_215, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_233 = x_215;
} else {
 lean_dec_ref(x_215);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_212);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
lean_free_object(x_8);
lean_dec(x_38);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_235 = lean_ctor_get(x_213, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_236 = x_213;
} else {
 lean_dec_ref(x_213);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
default: 
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_inc(x_182);
x_238 = l_Lean_Expr_app___override(x_38, x_182);
lean_inc(x_182);
x_239 = l_Lean_Expr_app___override(x_180, x_182);
if (lean_is_scalar(x_181)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_181;
}
lean_ctor_set(x_240, 0, x_179);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_178);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_8, 1, x_241);
lean_ctor_set(x_8, 0, x_238);
x_14 = x_8;
x_15 = lean_box(0);
goto block_19;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_242 = lean_ctor_get(x_8, 0);
lean_inc(x_242);
lean_dec(x_8);
x_243 = lean_ctor_get(x_35, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_244 = x_35;
} else {
 lean_dec_ref(x_35);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_36, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_36, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_247 = x_36;
} else {
 lean_dec_ref(x_36);
 x_247 = lean_box(0);
}
lean_inc_ref(x_2);
x_248 = lean_array_get_borrowed(x_2, x_3, x_7);
x_249 = lean_array_fget_borrowed(x_4, x_7);
x_250 = lean_unbox(x_249);
switch (x_250) {
case 1:
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_247);
lean_dec(x_244);
x_251 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_252 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_245, x_246, x_243, x_242, x_251, x_9, x_10, x_11, x_12);
x_20 = x_252;
goto block_32;
}
case 2:
{
lean_object* x_253; 
lean_dec(x_247);
lean_dec(x_244);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_5);
lean_inc(x_248);
x_253 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_248, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
lean_inc(x_255);
x_258 = l_Lean_Expr_app___override(x_242, x_255);
lean_inc(x_256);
lean_inc(x_248);
x_259 = l_Lean_mkApp3(x_246, x_248, x_255, x_256);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_257);
x_260 = lean_box(0);
x_261 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_256, x_245, x_259, x_258, x_243, x_260, x_9, x_10, x_11, x_12);
lean_dec(x_256);
x_20 = x_261;
goto block_32;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
lean_inc_ref(x_6);
x_263 = l_Lean_stringToMessageData(x_6);
if (lean_is_scalar(x_257)) {
 x_264 = lean_alloc_ctor(7, 2, 0);
} else {
 x_264 = x_257;
 lean_ctor_set_tag(x_264, 7);
}
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_266, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__1(x_256, x_245, x_259, x_258, x_243, x_268, x_9, x_10, x_11, x_12);
lean_dec_ref(x_243);
lean_dec(x_256);
x_20 = x_269;
goto block_32;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec(x_256);
lean_dec(x_245);
lean_dec_ref(x_243);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_270);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_273 = lean_ctor_get(x_253, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_274 = x_253;
} else {
 lean_dec_ref(x_253);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
case 4:
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_247);
lean_dec(x_244);
x_276 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_277 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0(x_245, x_246, x_243, x_242, x_276, x_9, x_10, x_11, x_12);
x_20 = x_277;
goto block_32;
}
case 5:
{
lean_object* x_278; lean_object* x_279; 
lean_inc(x_248);
x_278 = l_Lean_Expr_app___override(x_246, x_248);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_278);
x_279 = lean_infer_type(x_278, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec_ref(x_279);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_281 = lean_whnf(x_280, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_Expr_bindingDomain_x21(x_282);
lean_dec(x_282);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_285 = 0;
x_286 = lean_box(0);
lean_inc_ref(x_9);
x_287 = l_Lean_Meta_mkFreshExprMVar(x_284, x_285, x_286, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
lean_inc(x_288);
x_289 = l_Lean_Expr_app___override(x_242, x_288);
lean_inc(x_288);
x_290 = l_Lean_Expr_app___override(x_278, x_288);
x_291 = l_Lean_Expr_mvarId_x21(x_288);
lean_dec(x_288);
x_292 = lean_array_push(x_245, x_291);
if (lean_is_scalar(x_247)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_247;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_290);
if (lean_is_scalar(x_244)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_244;
}
lean_ctor_set(x_294, 0, x_243);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_289);
lean_ctor_set(x_295, 1, x_294);
x_14 = x_295;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec_ref(x_278);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_296 = lean_ctor_get(x_287, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_297 = x_287;
} else {
 lean_dec_ref(x_287);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_278);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_299 = lean_ctor_get(x_281, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_300 = x_281;
} else {
 lean_dec_ref(x_281);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec_ref(x_278);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_302 = lean_ctor_get(x_279, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 x_303 = x_279;
} else {
 lean_dec_ref(x_279);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
return x_304;
}
}
default: 
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_inc(x_248);
x_305 = l_Lean_Expr_app___override(x_242, x_248);
lean_inc(x_248);
x_306 = l_Lean_Expr_app___override(x_246, x_248);
if (lean_is_scalar(x_247)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_247;
}
lean_ctor_set(x_307, 0, x_245);
lean_ctor_set(x_307, 1, x_306);
if (lean_is_scalar(x_244)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_244;
}
lean_ctor_set(x_308, 0, x_243);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_305);
lean_ctor_set(x_309, 1, x_308);
x_14 = x_309;
x_15 = lean_box(0);
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
x_8 = x_14;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; 
lean_free_object(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_14 = x_24;
x_15 = lean_box(0);
goto block_19;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_14 = x_28;
x_15 = lean_box(0);
goto block_19;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1;
x_5 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic failed to create congruence theorem", 49, 49);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_get_size(x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_getFunInfoNArgs(x_3, x_39, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_getCongrSimpKindsForArgZero(x_41, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_45 = l_Lean_Meta_mkCongrSimpCore_x3f(x_3, x_41, x_43, x_44, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_49);
lean_dec(x_47);
x_50 = l_Lean_instInhabitedExpr;
x_75 = 0;
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_box(x_75);
x_78 = lean_array_get_borrowed(x_77, x_49, x_76);
x_79 = lean_unbox(x_78);
if (x_79 == 2)
{
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_80 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
x_81 = l_Lean_stringToMessageData(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_84, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
block_74:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_array_get_size(x_49);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_box(0);
x_59 = l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc_ref(x_51);
x_63 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg(x_56, x_50, x_4, x_49, x_2, x_1, x_57, x_62, x_51, x_52, x_53, x_54);
lean_dec_ref(x_49);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_nat_dec_le(x_56, x_57);
if (x_70 == 0)
{
x_18 = x_53;
x_19 = lean_box(0);
x_20 = x_52;
x_21 = x_68;
x_22 = x_54;
x_23 = x_67;
x_24 = x_51;
x_25 = x_69;
x_26 = x_56;
x_27 = x_39;
goto block_38;
}
else
{
x_18 = x_53;
x_19 = lean_box(0);
x_20 = x_52;
x_21 = x_68;
x_22 = x_54;
x_23 = x_67;
x_24 = x_51;
x_25 = x_69;
x_26 = x_57;
x_27 = x_39;
goto block_38;
}
}
else
{
uint8_t x_71; 
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_4);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
return x_63;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_46);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_89 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
x_90 = l_Lean_stringToMessageData(x_1);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_93, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_45);
if (x_95 == 0)
{
return x_45;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_45, 0);
lean_inc(x_96);
lean_dec(x_45);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_42);
if (x_98 == 0)
{
return x_42;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_42, 0);
lean_inc(x_99);
lean_dec(x_42);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_40);
if (x_101 == 0)
{
return x_40;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_40, 0);
lean_inc(x_102);
lean_dec(x_40);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_38:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Array_toSubarray___redArg(x_4, x_26, x_27);
x_29 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg(x_28, x_25, x_24, x_20, x_18, x_22);
if (lean_obj_tag(x_29) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3;
x_32 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(x_31);
x_10 = lean_box(0);
x_11 = x_21;
x_12 = x_30;
x_13 = x_32;
goto block_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec_ref(x_29);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec_ref(x_23);
x_10 = lean_box(0);
x_11 = x_21;
x_12 = x_33;
x_13 = x_34;
goto block_17;
}
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec_ref(x_21);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___redArg(x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pi_congr", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_getLevel(x_1, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_2);
x_17 = l_Lean_MVarId_getTag(x_2, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_expr_instantiate1(x_3, x_9);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_19);
x_20 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_19, x_18, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_25 = l_Lean_Meta_getLevel(x_19, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_28 = lean_array_push(x_27, x_9);
x_29 = 1;
x_30 = l_Lean_Meta_mkLambdaFVars(x_28, x_23, x_4, x_5, x_4, x_5, x_29, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_24);
x_32 = l_Lean_Meta_mkLambdaFVars(x_28, x_24, x_4, x_5, x_4, x_5, x_29, x_10, x_11, x_12, x_13);
lean_dec_ref(x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2;
x_35 = lean_box(0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_35);
lean_ctor_set(x_21, 0, x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_21);
x_37 = l_Lean_Expr_const___override(x_34, x_36);
x_38 = 0;
lean_inc_ref(x_1);
x_39 = l_Lean_Expr_lam___override(x_6, x_1, x_3, x_38);
x_40 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3;
x_41 = lean_array_push(x_40, x_1);
x_42 = lean_array_push(x_41, x_39);
x_43 = lean_array_push(x_42, x_31);
x_44 = lean_array_push(x_43, x_33);
x_45 = l_Lean_mkAppN(x_37, x_44);
lean_dec_ref(x_44);
lean_inc(x_11);
lean_inc_ref(x_45);
x_46 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_7, x_8, x_45, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_46);
x_47 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_2, x_45, x_11);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_35);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
x_52 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_35);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_45);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_31);
lean_dec(x_26);
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_32);
if (x_58 == 0)
{
return x_32;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_32, 0);
lean_inc(x_59);
lean_dec(x_32);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_28);
lean_dec(x_26);
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_30);
if (x_61 == 0)
{
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_30, 0);
lean_inc(x_62);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_25, 0);
lean_inc(x_65);
lean_dec(x_25);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_21, 0);
x_68 = lean_ctor_get(x_21, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_21);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_69 = l_Lean_Meta_getLevel(x_19, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_72 = lean_array_push(x_71, x_9);
x_73 = 1;
x_74 = l_Lean_Meta_mkLambdaFVars(x_72, x_67, x_4, x_5, x_4, x_5, x_73, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc(x_68);
x_76 = l_Lean_Meta_mkLambdaFVars(x_72, x_68, x_4, x_5, x_4, x_5, x_73, x_10, x_11, x_12, x_13);
lean_dec_ref(x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2;
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_16);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Expr_const___override(x_78, x_81);
x_83 = 0;
lean_inc_ref(x_1);
x_84 = l_Lean_Expr_lam___override(x_6, x_1, x_3, x_83);
x_85 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3;
x_86 = lean_array_push(x_85, x_1);
x_87 = lean_array_push(x_86, x_84);
x_88 = lean_array_push(x_87, x_75);
x_89 = lean_array_push(x_88, x_77);
x_90 = l_Lean_mkAppN(x_82, x_89);
lean_dec_ref(x_89);
lean_inc(x_11);
lean_inc_ref(x_90);
x_91 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_7, x_8, x_90, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_91);
x_92 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_2, x_90, x_11);
lean_dec(x_11);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_93 = x_92;
} else {
 lean_dec_ref(x_92);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Expr_mvarId_x21(x_68);
lean_dec(x_68);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_79);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 1, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_90);
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_2);
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_76, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_101 = x_76;
} else {
 lean_dec_ref(x_76);
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
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_74, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_104 = x_74;
} else {
 lean_dec_ref(x_74);
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
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_69, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_107 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
else
{
uint8_t x_109; 
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_20);
if (x_109 == 0)
{
return x_20;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_20, 0);
lean_inc(x_110);
lean_dec(x_20);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_17);
if (x_112 == 0)
{
return x_17;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_17, 0);
lean_inc(x_113);
lean_dec(x_17);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_15);
if (x_115 == 0)
{
return x_15;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_15, 0);
lean_inc(x_116);
lean_dec(x_15);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic failed, cannot select domain", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_prop_congr_dom", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Conv.congrArgForall", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_unsigned_to_nat(158u);
x_4 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5;
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
if (x_2 == 0)
{
lean_object* x_86; 
lean_dec_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_11);
x_86 = l_Lean_Core_mkFreshUserName(x_11, x_8, x_9);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = 1;
x_89 = lean_box(x_2);
x_90 = lean_box(x_88);
lean_inc_ref(x_12);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed), 14, 8);
lean_closure_set(x_91, 0, x_12);
lean_closure_set(x_91, 1, x_3);
lean_closure_set(x_91, 2, x_13);
lean_closure_set(x_91, 3, x_89);
lean_closure_set(x_91, 4, x_90);
lean_closure_set(x_91, 5, x_11);
lean_closure_set(x_91, 6, x_1);
lean_closure_set(x_91, 7, x_5);
x_92 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_87, x_12, x_91, x_6, x_7, x_8, x_9);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
x_96 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec_ref(x_4);
lean_inc(x_3);
x_97 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_99 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_12, x_98, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_13);
x_104 = l_Lean_Meta_mkEqRefl(x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1;
x_107 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4;
lean_inc(x_103);
x_108 = lean_array_push(x_107, x_103);
x_109 = lean_array_push(x_108, x_105);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_110 = l_Lean_Meta_mkAppM(x_106, x_109, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_3, x_111, x_7);
lean_dec_ref(x_112);
x_113 = l_Lean_Expr_forallE___override(x_11, x_102, x_13, x_14);
x_114 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_1, x_5, x_113, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
x_117 = l_Lean_Expr_mvarId_x21(x_103);
lean_dec(x_103);
x_118 = lean_box(0);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_118);
lean_ctor_set(x_100, 0, x_117);
lean_ctor_set(x_114, 0, x_100);
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_114);
x_119 = l_Lean_Expr_mvarId_x21(x_103);
lean_dec(x_103);
x_120 = lean_box(0);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_120);
lean_ctor_set(x_100, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_100);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_free_object(x_100);
lean_dec(x_103);
x_122 = !lean_is_exclusive(x_114);
if (x_122 == 0)
{
return x_114;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_100);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_110);
if (x_125 == 0)
{
return x_110;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_110, 0);
lean_inc(x_126);
lean_dec(x_110);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_100);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_104);
if (x_128 == 0)
{
return x_104;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_104, 0);
lean_inc(x_129);
lean_dec(x_104);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_100, 0);
x_132 = lean_ctor_get(x_100, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_100);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_13);
x_133 = l_Lean_Meta_mkEqRefl(x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1;
x_136 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4;
lean_inc(x_132);
x_137 = lean_array_push(x_136, x_132);
x_138 = lean_array_push(x_137, x_134);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_139 = l_Lean_Meta_mkAppM(x_135, x_138, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_3, x_140, x_7);
lean_dec_ref(x_141);
x_142 = l_Lean_Expr_forallE___override(x_11, x_131, x_13, x_14);
x_143 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_1, x_5, x_142, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_144 = x_143;
} else {
 lean_dec_ref(x_143);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Expr_mvarId_x21(x_132);
lean_dec(x_132);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(0, 1, 0);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_132);
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_150 = x_143;
} else {
 lean_dec_ref(x_143);
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
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_152 = lean_ctor_get(x_139, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_153 = x_139;
} else {
 lean_dec_ref(x_139);
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
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_133, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_156 = x_133;
} else {
 lean_dec_ref(x_133);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_158 = !lean_is_exclusive(x_99);
if (x_158 == 0)
{
return x_99;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_99, 0);
lean_inc(x_159);
lean_dec(x_99);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_161 = !lean_is_exclusive(x_97);
if (x_161 == 0)
{
return x_97;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_97, 0);
lean_inc(x_162);
lean_dec(x_97);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_13);
x_164 = l_Lean_Meta_isProp(x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_dec_ref(x_4);
x_15 = x_164;
goto block_85;
}
else
{
lean_object* x_167; 
lean_dec_ref(x_164);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_167 = l_Lean_Meta_isProp(x_4, x_6, x_7, x_8, x_9);
x_15 = x_167;
goto block_85;
}
}
else
{
lean_dec_ref(x_4);
x_15 = x_164;
goto block_85;
}
}
}
block_85:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec(x_3);
x_18 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
x_19 = l_Lean_stringToMessageData(x_1);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_22, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_3);
x_24 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_26 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_12, x_25, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3;
x_32 = 0;
x_33 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_32);
x_34 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4;
lean_inc(x_29);
x_35 = lean_array_push(x_34, x_29);
x_36 = lean_array_push(x_35, x_33);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = l_Lean_Meta_mkAppM(x_31, x_36, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_7);
lean_inc(x_38);
x_39 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_1, x_5, x_38, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_39);
x_40 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_3, x_38, x_7);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
x_44 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_44);
lean_ctor_set(x_27, 0, x_43);
lean_ctor_set(x_40, 0, x_27);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
x_45 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
x_46 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_27);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_37, 0);
lean_inc(x_52);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_dec(x_27);
x_55 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3;
x_56 = 0;
x_57 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_56);
x_58 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4;
lean_inc(x_54);
x_59 = lean_array_push(x_58, x_54);
x_60 = lean_array_push(x_59, x_57);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_61 = l_Lean_Meta_mkAppM(x_55, x_60, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_7);
lean_inc(x_62);
x_63 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_1, x_5, x_62, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_63);
x_64 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_3, x_62, x_7);
lean_dec(x_7);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_65 = x_64;
} else {
 lean_dec_ref(x_64);
 x_65 = lean_box(0);
}
x_66 = l_Lean_Expr_mvarId_x21(x_54);
lean_dec(x_54);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_3);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_26);
if (x_76 == 0)
{
return x_26;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
lean_dec(x_26);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_24, 0);
lean_inc(x_80);
lean_dec(x_24);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_15);
if (x_82 == 0)
{
return x_15;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_15, 0);
lean_inc(x_83);
lean_dec(x_15);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_168 = l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6;
x_169 = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(x_168, x_6, x_7, x_8, x_9);
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Elab_Tactic_Conv_congrArgForall(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec_ref(x_3);
x_13 = l_Lean_BinderInfo_isExplicit(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_push(x_2, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1;
x_24 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_23, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_11;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_29; 
x_29 = lean_nat_dec_lt(x_3, x_1);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec_ref(x_4);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isForall(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_Context_config(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_39 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_5, 2);
x_41 = lean_ctor_get(x_5, 3);
x_42 = lean_ctor_get(x_5, 4);
x_43 = lean_ctor_get(x_5, 5);
x_44 = lean_ctor_get(x_5, 6);
x_45 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_48 = 0;
lean_ctor_set_uint8(x_36, 9, x_48);
x_49 = l_Lean_Meta_Context_configKey(x_5);
x_50 = 2;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_expr_instantiate_rev_range(x_33, x_34, x_3, x_2);
lean_dec(x_34);
lean_dec(x_33);
x_53 = lean_uint64_shift_left(x_51, x_50);
x_54 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0;
x_55 = lean_uint64_lor(x_53, x_54);
x_56 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set_uint64(x_56, sizeof(void*)*1, x_55);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
x_57 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_40);
lean_ctor_set(x_57, 3, x_41);
lean_ctor_set(x_57, 4, x_42);
lean_ctor_set(x_57, 5, x_43);
lean_ctor_set(x_57, 6, x_44);
lean_ctor_set_uint8(x_57, sizeof(void*)*7, x_38);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 1, x_45);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 2, x_46);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 3, x_47);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_58 = lean_whnf(x_52, x_57, x_6, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
lean_inc_n(x_3, 2);
x_61 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(x_3, x_32, x_59, x_3, x_60, x_5, x_6, x_7, x_8);
x_10 = x_61;
goto block_28;
}
else
{
uint8_t x_62; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_65 = lean_ctor_get_uint8(x_36, 0);
x_66 = lean_ctor_get_uint8(x_36, 1);
x_67 = lean_ctor_get_uint8(x_36, 2);
x_68 = lean_ctor_get_uint8(x_36, 3);
x_69 = lean_ctor_get_uint8(x_36, 4);
x_70 = lean_ctor_get_uint8(x_36, 5);
x_71 = lean_ctor_get_uint8(x_36, 6);
x_72 = lean_ctor_get_uint8(x_36, 7);
x_73 = lean_ctor_get_uint8(x_36, 8);
x_74 = lean_ctor_get_uint8(x_36, 10);
x_75 = lean_ctor_get_uint8(x_36, 11);
x_76 = lean_ctor_get_uint8(x_36, 12);
x_77 = lean_ctor_get_uint8(x_36, 13);
x_78 = lean_ctor_get_uint8(x_36, 14);
x_79 = lean_ctor_get_uint8(x_36, 15);
x_80 = lean_ctor_get_uint8(x_36, 16);
x_81 = lean_ctor_get_uint8(x_36, 17);
x_82 = lean_ctor_get_uint8(x_36, 18);
lean_dec(x_36);
x_83 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 2);
x_86 = lean_ctor_get(x_5, 3);
x_87 = lean_ctor_get(x_5, 4);
x_88 = lean_ctor_get(x_5, 5);
x_89 = lean_ctor_get(x_5, 6);
x_90 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_91 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_92 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_93 = 0;
x_94 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_94, 0, x_65);
lean_ctor_set_uint8(x_94, 1, x_66);
lean_ctor_set_uint8(x_94, 2, x_67);
lean_ctor_set_uint8(x_94, 3, x_68);
lean_ctor_set_uint8(x_94, 4, x_69);
lean_ctor_set_uint8(x_94, 5, x_70);
lean_ctor_set_uint8(x_94, 6, x_71);
lean_ctor_set_uint8(x_94, 7, x_72);
lean_ctor_set_uint8(x_94, 8, x_73);
lean_ctor_set_uint8(x_94, 9, x_93);
lean_ctor_set_uint8(x_94, 10, x_74);
lean_ctor_set_uint8(x_94, 11, x_75);
lean_ctor_set_uint8(x_94, 12, x_76);
lean_ctor_set_uint8(x_94, 13, x_77);
lean_ctor_set_uint8(x_94, 14, x_78);
lean_ctor_set_uint8(x_94, 15, x_79);
lean_ctor_set_uint8(x_94, 16, x_80);
lean_ctor_set_uint8(x_94, 17, x_81);
lean_ctor_set_uint8(x_94, 18, x_82);
x_95 = l_Lean_Meta_Context_configKey(x_5);
x_96 = 2;
x_97 = lean_uint64_shift_right(x_95, x_96);
x_98 = lean_expr_instantiate_rev_range(x_33, x_34, x_3, x_2);
lean_dec(x_34);
lean_dec(x_33);
x_99 = lean_uint64_shift_left(x_97, x_96);
x_100 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0;
x_101 = lean_uint64_lor(x_99, x_100);
x_102 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_102, 0, x_94);
lean_ctor_set_uint64(x_102, sizeof(void*)*1, x_101);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc_ref(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
x_103 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_84);
lean_ctor_set(x_103, 2, x_85);
lean_ctor_set(x_103, 3, x_86);
lean_ctor_set(x_103, 4, x_87);
lean_ctor_set(x_103, 5, x_88);
lean_ctor_set(x_103, 6, x_89);
lean_ctor_set_uint8(x_103, sizeof(void*)*7, x_83);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 1, x_90);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 2, x_91);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 3, x_92);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_104 = lean_whnf(x_98, x_103, x_6, x_7, x_8);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = lean_box(0);
lean_inc_n(x_3, 2);
x_107 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(x_3, x_32, x_105, x_3, x_106, x_5, x_6, x_7, x_8);
x_10 = x_107;
goto block_28;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_box(0);
lean_inc(x_3);
x_112 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(x_3, x_32, x_33, x_34, x_111, x_5, x_6, x_7, x_8);
x_10 = x_112;
goto block_28;
}
}
block_28:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
x_4 = x_21;
goto _start;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` tactic, application has ", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" explicit argument(s) but the index is out of bounds", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" argument(s) but the index is out of bounds", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
if (x_2 == 0)
{
lean_object* x_29; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
x_29 = lean_infer_type(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_array_get_size(x_4);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_36 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(x_31, x_4, x_32, x_35, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_49; lean_object* x_67; lean_object* x_68; uint8_t x_74; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_67 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
x_74 = lean_int_dec_lt(x_67, x_5);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_array_get_size(x_38);
x_76 = lean_nat_to_int(x_75);
x_77 = lean_int_add(x_5, x_76);
lean_dec(x_76);
x_68 = x_77;
goto block_73;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
x_79 = lean_int_sub(x_5, x_78);
x_68 = x_79;
goto block_73;
}
block_48:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_nat_abs(x_40);
lean_dec(x_40);
x_43 = lean_array_get(x_32, x_38, x_42);
lean_dec(x_42);
lean_dec(x_38);
lean_inc(x_43);
lean_inc_ref(x_4);
x_44 = l_Array_toSubarray___redArg(x_4, x_32, x_43);
x_45 = l_Subarray_toArray___redArg(x_44);
x_46 = l_Lean_mkAppN(x_3, x_45);
lean_dec_ref(x_45);
x_47 = lean_nat_dec_le(x_43, x_32);
if (x_47 == 0)
{
x_20 = lean_box(0);
x_21 = x_46;
x_22 = x_43;
x_23 = x_31;
goto block_28;
}
else
{
lean_dec(x_43);
x_20 = lean_box(0);
x_21 = x_46;
x_22 = x_32;
x_23 = x_31;
goto block_28;
}
}
block_66:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_49);
x_50 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_51 = l_Lean_stringToMessageData(x_1);
if (lean_is_scalar(x_39)) {
 x_52 = lean_alloc_ctor(7, 2, 0);
} else {
 x_52 = x_39;
 lean_ctor_set_tag(x_52, 7);
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_get_size(x_38);
lean_dec(x_38);
x_56 = l_Nat_reprFast(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_61, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
block_73:
{
uint8_t x_69; 
x_69 = lean_int_dec_lt(x_68, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_array_get_size(x_38);
x_71 = lean_nat_to_int(x_70);
x_72 = lean_int_dec_le(x_71, x_68);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_39);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_40 = x_68;
x_41 = lean_box(0);
goto block_48;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_49 = x_68;
goto block_66;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_49 = x_68;
goto block_66;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_36);
if (x_80 == 0)
{
return x_36;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_36, 0);
lean_inc(x_81);
lean_dec(x_36);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_96; lean_object* x_114; lean_object* x_115; uint8_t x_121; 
x_86 = lean_unsigned_to_nat(0u);
x_114 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
x_121 = lean_int_dec_lt(x_114, x_5);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_array_get_size(x_4);
x_123 = lean_nat_to_int(x_122);
x_124 = lean_int_add(x_5, x_123);
lean_dec(x_123);
x_115 = x_124;
goto block_120;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
x_126 = lean_int_sub(x_5, x_125);
x_115 = x_126;
goto block_120;
}
block_95:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_89 = lean_nat_abs(x_87);
lean_dec(x_87);
lean_inc(x_89);
lean_inc_ref(x_4);
x_90 = l_Array_toSubarray___redArg(x_4, x_86, x_89);
x_91 = l_Subarray_toArray___redArg(x_90);
x_92 = l_Lean_mkAppN(x_3, x_91);
lean_dec_ref(x_91);
x_93 = lean_array_get_size(x_4);
x_94 = lean_nat_dec_le(x_89, x_86);
if (x_94 == 0)
{
x_11 = x_92;
x_12 = lean_box(0);
x_13 = x_89;
x_14 = x_93;
goto block_19;
}
else
{
lean_dec(x_89);
x_11 = x_92;
x_12 = lean_box(0);
x_13 = x_86;
x_14 = x_93;
goto block_19;
}
}
block_113:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_96);
x_97 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_98 = l_Lean_stringToMessageData(x_1);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_get_size(x_4);
lean_dec_ref(x_4);
x_103 = l_Nat_reprFast(x_102);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_MessageData_ofFormat(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_108, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
block_120:
{
uint8_t x_116; 
x_116 = lean_int_dec_lt(x_115, x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_array_get_size(x_4);
x_118 = lean_nat_to_int(x_117);
x_119 = lean_int_dec_le(x_118, x_115);
lean_dec(x_118);
if (x_119 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_87 = x_115;
x_88 = lean_box(0);
goto block_95;
}
else
{
lean_dec_ref(x_3);
x_96 = x_115;
goto block_113;
}
}
else
{
lean_dec_ref(x_3);
x_96 = x_115;
goto block_113;
}
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Array_toSubarray___redArg(x_4, x_13, x_14);
x_16 = l_Subarray_toArray___redArg(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Array_toSubarray___redArg(x_4, x_22, x_23);
x_25 = l_Subarray_toArray___redArg(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_6);
x_16 = lean_array_set(x_7, x_8, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
lean_dec(x_8);
x_6 = x_14;
x_7 = x_16;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_20 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(x_1, x_2, x_6, x_7, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_4);
x_24 = l_Lean_MVarId_getTag(x_4, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_26 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(x_1, x_25, x_22, x_23, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_10);
lean_inc(x_29);
x_33 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_1, x_5, x_29, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec_ref(x_33);
x_34 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_4, x_29, x_10);
lean_dec(x_10);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_array_to_list(x_32);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_34, 0, x_28);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_38 = lean_array_to_list(x_32);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_28);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_28);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_29);
x_45 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(x_1, x_5, x_29, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_45);
x_46 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_4, x_29, x_10);
lean_dec(x_10);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_47 = x_46;
} else {
 lean_dec_ref(x_46);
 x_47 = lean_box(0);
}
x_48 = lean_array_to_list(x_44);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_4);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_24, 0);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_inc(x_61);
lean_dec(x_20);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic, index is out of bounds for pi type", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` conv tactic, application or implication expected", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_41; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_12, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Expr_cleanupAnnotations(x_16);
x_18 = l_Lean_Expr_isForall(x_17);
if (x_18 == 0)
{
uint8_t x_45; 
lean_dec(x_14);
x_45 = l_Lean_Expr_isApp(x_17);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_1);
x_46 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_47 = l_Lean_stringToMessageData(x_2);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_17);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_52, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
x_55 = l_Lean_Expr_getAppNumArgs(x_17);
lean_inc(x_55);
x_56 = lean_mk_array(x_55, x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_55, x_57);
lean_dec(x_55);
x_59 = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(x_2, x_3, x_4, x_1, x_13, x_17, x_56, x_58, x_5, x_6, x_7, x_8);
return x_59;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1;
x_61 = lean_int_dec_lt(x_4, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
x_63 = lean_int_dec_eq(x_4, x_62);
x_41 = x_63;
goto block_44;
}
else
{
x_41 = x_18;
goto block_44;
}
}
block_30:
{
lean_object* x_24; uint8_t x_25; 
x_24 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
x_25 = lean_int_dec_eq(x_4, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1;
x_27 = lean_int_dec_eq(x_4, x_26);
x_28 = l_Lean_Elab_Tactic_Conv_congrArgForall(x_2, x_27, x_1, x_17, x_13, x_19, x_20, x_21, x_22);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Tactic_Conv_congrArgForall(x_2, x_18, x_1, x_17, x_13, x_19, x_20, x_21, x_22);
return x_29;
}
}
block_40:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
x_32 = l_Lean_stringToMessageData(x_2);
if (lean_is_scalar(x_14)) {
 x_33 = lean_alloc_ctor(7, 2, 0);
} else {
 x_33 = x_14;
 lean_ctor_set_tag(x_33, 7);
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_35, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
block_44:
{
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0;
x_43 = lean_int_dec_lt(x_42, x_4);
if (x_43 == 0)
{
lean_dec(x_14);
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = lean_box(0);
goto block_30;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec(x_1);
goto block_40;
}
}
else
{
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec(x_1);
goto block_40;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_10, 0);
lean_inc(x_65);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_4);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_3);
x_12 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_2, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Elab_Tactic_Conv_congrArgN(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
x_11 = lean_int_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_5, x_6, x_7, x_8);
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
x_14 = l_Lean_Elab_Tactic_Conv_congrArgN(x_1, x_13, x_2, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_15, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_25 = l_Lean_Elab_Tactic_Conv_congrFunN(x_24, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_28, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_Conv_evalArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_elabArg___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_elabArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("argArg", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_elabArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; uint8_t x_38; 
x_11 = l_Lean_Elab_Tactic_Conv_elabArg___closed__0;
x_37 = l_Lean_Elab_Tactic_Conv_elabArg___closed__1;
lean_inc(x_1);
x_38 = l_Lean_Syntax_isOfKind(x_1, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_39 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_62; uint8_t x_63; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
lean_dec(x_1);
x_62 = l_Lean_Elab_Tactic_Conv_elabArg___closed__5;
lean_inc(x_41);
x_63 = l_Lean_Syntax_isOfKind(x_41, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_64 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_84; uint8_t x_85; 
x_65 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Syntax_getArg(x_41, x_65);
x_85 = l_Lean_Syntax_isNone(x_84);
if (x_85 == 0)
{
uint8_t x_86; 
lean_inc(x_84);
x_86 = l_Lean_Syntax_matchesNull(x_84, x_40);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_87 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Syntax_getArg(x_84, x_65);
lean_dec(x_84);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_66 = x_89;
x_67 = x_2;
x_68 = x_3;
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = x_8;
x_74 = x_9;
x_75 = lean_box(0);
goto block_83;
}
}
else
{
lean_object* x_90; 
lean_dec(x_84);
x_90 = lean_box(0);
x_66 = x_90;
x_67 = x_2;
x_68 = x_3;
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = x_8;
x_74 = x_9;
x_75 = lean_box(0);
goto block_83;
}
block_83:
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_Syntax_getArg(x_41, x_40);
x_77 = l_Lean_Syntax_isNone(x_76);
if (x_77 == 0)
{
uint8_t x_78; 
lean_inc(x_76);
x_78 = l_Lean_Syntax_matchesNull(x_76, x_40);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_66);
lean_dec(x_41);
x_79 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Syntax_getArg(x_76, x_65);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_42 = x_66;
x_43 = x_81;
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_74;
x_52 = lean_box(0);
goto block_61;
}
}
else
{
lean_object* x_82; 
lean_dec(x_76);
x_82 = lean_box(0);
x_42 = x_66;
x_43 = x_82;
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_74;
x_52 = lean_box(0);
goto block_61;
}
}
}
block_61:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = l_Lean_Syntax_getArg(x_41, x_53);
lean_dec(x_41);
x_55 = l_Lean_Elab_Tactic_Conv_elabArg___closed__3;
lean_inc(x_54);
x_56 = l_Lean_Syntax_isOfKind(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_42);
x_57 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return x_57;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
x_25 = x_56;
x_26 = x_48;
x_27 = x_50;
x_28 = x_45;
x_29 = x_54;
x_30 = lean_box(0);
x_31 = x_42;
x_32 = x_49;
x_33 = x_51;
goto block_36;
}
else
{
lean_dec_ref(x_43);
if (x_56 == 0)
{
x_25 = x_56;
x_26 = x_48;
x_27 = x_50;
x_28 = x_45;
x_29 = x_54;
x_30 = lean_box(0);
x_31 = x_42;
x_32 = x_49;
x_33 = x_51;
goto block_36;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l_Lean_TSyntax_getNat(x_54);
lean_dec(x_54);
x_59 = lean_nat_to_int(x_58);
x_60 = lean_int_neg(x_59);
lean_dec(x_59);
x_12 = x_56;
x_13 = x_50;
x_14 = x_48;
x_15 = x_45;
x_16 = lean_box(0);
x_17 = x_42;
x_18 = x_49;
x_19 = x_51;
x_20 = x_60;
goto block_24;
}
}
}
}
}
block_24:
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_11, x_20, x_21, x_15, x_14, x_18, x_13, x_19);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_17);
x_23 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_11, x_20, x_12, x_15, x_14, x_18, x_13, x_19);
return x_23;
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_TSyntax_getNat(x_29);
lean_dec(x_29);
x_35 = lean_nat_to_int(x_34);
x_12 = x_25;
x_13 = x_27;
x_14 = x_26;
x_15 = x_28;
x_16 = lean_box(0);
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_35;
goto block_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_elabArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabArg", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_elabArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lhs", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0;
x_8 = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1;
x_9 = 0;
x_10 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalLhs", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0;
x_4 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(97u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = lean_unsigned_to_nat(99u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(97u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(97u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rhs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0;
x_8 = l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1;
x_9 = 0;
x_10 = l_Lean_Elab_Tactic_Conv_evalArg___redArg(x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRhs", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0;
x_4 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(101u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = lean_unsigned_to_nat(103u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(101u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(101u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_9, x_1, x_2);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_23 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_21, x_1, x_2);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(x_40, x_1, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 9, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_43);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_31);
lean_ctor_set(x_45, 4, x_32);
x_46 = lean_st_ref_set(x_3, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'fun' conv tactic, application expected", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_11 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(x_14, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
if (lean_obj_tag(x_18) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_22 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_19, x_21, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_20);
lean_inc(x_26);
x_27 = l_Lean_Meta_mkCongrFun(x_26, x_20, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(x_1, x_28, x_7);
lean_dec_ref(x_29);
x_30 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0;
x_31 = l_Lean_Expr_app___override(x_25, x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_32 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_30, x_15, x_31, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_32);
x_33 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_34 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_34);
lean_ctor_set(x_23, 0, x_33);
x_35 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_23, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_35;
}
else
{
lean_free_object(x_23);
lean_dec(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_32;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_23);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_20);
lean_inc(x_40);
x_41 = l_Lean_Meta_mkCongrFun(x_40, x_20, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(x_1, x_42, x_7);
lean_dec_ref(x_43);
x_44 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0;
x_45 = l_Lean_Expr_app___override(x_39, x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_46 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_44, x_15, x_45, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_46);
x_47 = l_Lean_Expr_mvarId_x21(x_40);
lean_dec(x_40);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_49, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_50;
}
else
{
lean_dec(x_40);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_46;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
return x_22;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_1);
x_57 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2;
x_58 = l_Lean_indentExpr(x_18);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_58);
lean_ctor_set(x_12, 0, x_57);
x_59 = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(x_12, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_12, 0);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_12);
x_62 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(x_60, x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Expr_cleanupAnnotations(x_63);
if (lean_obj_tag(x_64) == 5)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_66);
lean_dec_ref(x_64);
x_67 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_68 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_65, x_67, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_66);
lean_inc(x_71);
x_73 = l_Lean_Meta_mkCongrFun(x_71, x_66, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(x_1, x_74, x_7);
lean_dec_ref(x_75);
x_76 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0;
x_77 = l_Lean_Expr_app___override(x_70, x_66);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_78 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_76, x_61, x_77, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_78);
x_79 = l_Lean_Expr_mvarId_x21(x_71);
lean_dec(x_71);
x_80 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_72;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_81, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_82;
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_78;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_66);
lean_dec(x_61);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_66);
lean_dec(x_61);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_87 = x_68;
} else {
 lean_dec_ref(x_68);
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
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_61);
lean_dec(x_1);
x_89 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2;
x_90 = l_Lean_indentExpr(x_64);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(x_91, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
return x_11;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_11, 0);
lean_inc(x_94);
lean_dec(x_11);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_evalFun___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalFun___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(x_1, x_2, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalFun", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0;
x_4 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(131u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(37u);
x_2 = lean_unsigned_to_nat(143u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(37u);
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(52u);
x_2 = lean_unsigned_to_nat(131u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = lean_unsigned_to_nat(131u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(52u);
x_4 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to go inside let-declaration, type error", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_6);
x_12 = l_Lean_Expr_app___override(x_1, x_6);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_13 = lean_infer_type(x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_16 = lean_array_push(x_15, x_6);
x_17 = 0;
x_18 = 1;
x_19 = 1;
lean_inc(x_14);
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_14, x_17, x_18, x_17, x_18, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_14);
x_22 = l_Lean_Meta_getLevel(x_14, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_14);
x_25 = 0;
x_26 = lean_box(0);
lean_inc_ref(x_7);
x_27 = l_Lean_Meta_mkFreshExprMVar(x_24, x_25, x_26, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_mkLambdaFVars(x_16, x_28, x_17, x_18, x_17, x_18, x_19, x_7, x_8, x_9, x_10);
lean_dec_ref(x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_37 = l_Lean_Expr_bindingBody_x21(x_30);
x_38 = l_Lean_Expr_letE___override(x_2, x_3, x_4, x_37, x_17);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_39 = l_Lean_Meta_isExprDefEq(x_5, x_38, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_21);
x_42 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1;
x_43 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_42, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_32 = lean_box(0);
goto block_36;
}
}
else
{
uint8_t x_47; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
return x_27;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_27, 0);
lean_inc(x_54);
lean_dec(x_27);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_22, 0);
lean_inc(x_57);
lean_dec(x_22);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_20);
if (x_59 == 0)
{
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
return x_13;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
lean_dec(x_13);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_10 = lean_array_push(x_9, x_3);
lean_inc_ref(x_10);
x_11 = l_Lean_Expr_beta(x_1, x_10);
lean_inc_ref(x_10);
x_12 = l_Lean_Expr_beta(x_2, x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = l_Lean_Meta_mkEq(x_11, x_12, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
lean_inc_ref(x_4);
x_16 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_14, x_15, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = 0;
x_19 = 1;
x_20 = 1;
lean_inc(x_17);
x_21 = l_Lean_Meta_mkLambdaFVars(x_10, x_17, x_18, x_19, x_18, x_19, x_20, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let_body_congr", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to abstract let-expression, result is not type correct", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_10);
x_13 = l_Lean_Meta_getLevel(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 0;
lean_inc_ref(x_10);
lean_inc(x_9);
x_16 = l_Lean_mkLambda(x_9, x_15, x_10, x_12);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_16);
x_17 = l_Lean_Meta_isTypeCorrect(x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_112; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_10);
lean_closure_set(x_19, 3, x_11);
lean_closure_set(x_19, 4, x_3);
x_112 = lean_unbox(x_18);
lean_dec(x_18);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_113 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3;
x_114 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_113, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = lean_box(0);
goto block_111;
}
block_111:
{
lean_object* x_25; 
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_9, x_10, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc_ref(x_16);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_32, 0, x_16);
lean_closure_set(x_32, 1, x_31);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_10);
x_33 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_9, x_10, x_32, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1;
x_39 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_39);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_14);
x_40 = l_Lean_mkConst(x_38, x_27);
x_41 = l_Lean_mkApp6(x_40, x_10, x_28, x_16, x_31, x_11, x_36);
x_42 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_41, x_21);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_37, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_47);
lean_ctor_set(x_45, 0, x_42);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_48);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_42);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_42);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_42);
x_53 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_37, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_63 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1;
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_30);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_65);
lean_ctor_set(x_27, 0, x_14);
x_66 = l_Lean_mkConst(x_63, x_27);
x_67 = l_Lean_mkApp6(x_66, x_10, x_28, x_16, x_31, x_11, x_61);
x_68 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_67, x_21);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_69 = x_68;
} else {
 lean_dec_ref(x_68);
 x_69 = lean_box(0);
}
x_70 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_62, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_69;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_71);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_69);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_free_object(x_27);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_33, 0);
lean_inc(x_79);
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_27, 0);
x_82 = lean_ctor_get(x_27, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_27);
lean_inc(x_82);
lean_inc_ref(x_16);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_83, 0, x_16);
lean_closure_set(x_83, 1, x_82);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_10);
x_84 = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(x_9, x_10, x_83, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1;
x_90 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_88;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_14);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_mkConst(x_89, x_92);
x_94 = l_Lean_mkApp6(x_93, x_10, x_28, x_16, x_82, x_11, x_86);
x_95 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_94, x_21);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_96 = x_95;
} else {
 lean_dec_ref(x_95);
 x_96 = lean_box(0);
}
x_97 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_87, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_96;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_98);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_96);
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_103 = x_97;
} else {
 lean_dec_ref(x_97);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_28);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_105 = lean_ctor_get(x_84, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_106 = x_84;
} else {
 lean_dec_ref(x_84);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_25);
if (x_108 == 0)
{
return x_25;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_25, 0);
lean_inc(x_109);
lean_dec(x_25);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_17);
if (x_118 == 0)
{
return x_17;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_17, 0);
lean_inc(x_119);
lean_dec(x_17);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_13);
if (x_121 == 0)
{
return x_13;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_13, 0);
lean_inc(x_122);
lean_dec(x_13);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ext", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = lean_box(0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_9, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_17 = lean_array_push(x_16, x_3);
x_18 = 0;
x_19 = 1;
x_20 = 1;
lean_inc(x_14);
x_21 = l_Lean_Meta_mkLambdaFVars(x_17, x_14, x_18, x_19, x_18, x_19, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_15);
x_23 = l_Lean_Meta_mkLambdaFVars(x_17, x_15, x_18, x_19, x_18, x_19, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_mkForallFVars(x_17, x_14, x_18, x_19, x_19, x_20, x_4, x_5, x_6, x_7);
lean_dec_ref(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
x_28 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_27, x_2, x_26, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_12, 0, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_ctor_set(x_12, 0, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_12);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_12);
lean_dec(x_15);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_17);
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0;
x_49 = lean_array_push(x_48, x_3);
x_50 = 0;
x_51 = 1;
x_52 = 1;
lean_inc(x_46);
x_53 = l_Lean_Meta_mkLambdaFVars(x_49, x_46, x_50, x_51, x_50, x_51, x_52, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_47);
x_55 = l_Lean_Meta_mkLambdaFVars(x_49, x_47, x_50, x_51, x_50, x_51, x_52, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_mkForallFVars(x_49, x_46, x_50, x_51, x_51, x_52, x_4, x_5, x_6, x_7);
lean_dec_ref(x_49);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
x_60 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(x_59, x_2, x_58, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_61 = x_60;
} else {
 lean_dec_ref(x_60);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_47);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_47);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_47);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_69 = x_57;
} else {
 lean_dec_ref(x_57);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_54);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_53, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_75 = x_53;
} else {
 lean_dec_ref(x_53);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_77 = !lean_is_exclusive(x_11);
if (x_77 == 0)
{
return x_11;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_11, 0);
lean_inc(x_78);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_3, x_4, x_5, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(x_1, x_2, x_3, x_12, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'apply funext' unexpected result", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funext", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_congr", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'ext' conv tactic, function or arrow expected", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_65; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_65 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_68, x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_Expr_cleanupAnnotations(x_71);
if (lean_obj_tag(x_72) == 7)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
lean_free_object(x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc_ref(x_75);
x_76 = lean_ctor_get_uint8(x_72, sizeof(void*)*3 + 8);
lean_dec_ref(x_72);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_74);
x_77 = l_Lean_Meta_getLevel(x_74, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
lean_inc_ref(x_75);
lean_inc_ref(x_74);
lean_inc(x_73);
x_79 = l_Lean_Expr_lam___override(x_73, x_74, x_75, x_76);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_119; 
lean_dec(x_73);
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
lean_dec_ref(x_2);
x_80 = x_119;
x_81 = x_3;
x_82 = x_4;
x_83 = x_5;
x_84 = x_6;
x_85 = lean_box(0);
goto block_118;
}
else
{
lean_object* x_120; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_120 = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(x_73, x_3, x_5, x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_80 = x_121;
x_81 = x_3;
x_82 = x_4;
x_83 = x_5;
x_84 = x_6;
x_85 = lean_box(0);
goto block_118;
}
else
{
uint8_t x_122; 
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_69);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
block_118:
{
uint8_t x_86; lean_object* x_87; 
x_86 = 0;
lean_inc(x_82);
lean_inc_ref(x_74);
x_87 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(x_75, x_69, x_80, x_76, x_74, x_86, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 1);
x_94 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5;
x_95 = lean_box(0);
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 1, x_95);
lean_ctor_set(x_89, 0, x_78);
x_96 = l_Lean_mkConst(x_94, x_89);
x_97 = l_Lean_mkApp4(x_96, x_74, x_79, x_90, x_92);
x_98 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_97, x_82);
lean_dec(x_82);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
x_101 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_98);
x_102 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_89, 0);
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_89);
x_106 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5;
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_78);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_mkConst(x_106, x_108);
x_110 = l_Lean_mkApp4(x_109, x_74, x_79, x_90, x_104);
x_111 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_110, x_82);
lean_dec(x_82);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_112 = x_111;
} else {
 lean_dec_ref(x_111);
 x_112 = lean_box(0);
}
x_113 = l_Lean_Expr_mvarId_x21(x_105);
lean_dec(x_105);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_82);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_74);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_87);
if (x_115 == 0)
{
return x_87;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_87, 0);
lean_inc(x_116);
lean_dec(x_87);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_77);
if (x_125 == 0)
{
return x_77;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_77, 0);
lean_inc(x_126);
lean_dec(x_77);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_72);
lean_inc(x_1);
x_128 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(x_1, x_72, x_69, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; 
lean_free_object(x_128);
lean_dec(x_130);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_72);
x_132 = lean_infer_type(x_72, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_134 = l_Lean_Meta_whnfD(x_133, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Expr_isForall(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_2);
lean_dec(x_1);
x_137 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7;
x_138 = l_Lean_MessageData_ofExpr(x_72);
x_139 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9;
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_139);
lean_ctor_set(x_66, 0, x_138);
x_140 = l_Lean_MessageData_ofExpr(x_135);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_66);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_indentD(x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_143, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
else
{
lean_dec(x_135);
lean_dec_ref(x_72);
lean_free_object(x_66);
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = lean_box(0);
goto block_64;
}
}
else
{
uint8_t x_148; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_134);
if (x_148 == 0)
{
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
lean_dec(x_134);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_132);
if (x_151 == 0)
{
return x_132;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_132, 0);
lean_inc(x_152);
lean_dec(x_132);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_128, 0);
lean_inc(x_154);
lean_dec(x_128);
if (lean_obj_tag(x_154) == 1)
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; 
lean_dec(x_154);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_72);
x_157 = lean_infer_type(x_72, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_159 = l_Lean_Meta_whnfD(x_158, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = l_Lean_Expr_isForall(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
lean_dec(x_1);
x_162 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7;
x_163 = l_Lean_MessageData_ofExpr(x_72);
x_164 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9;
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_164);
lean_ctor_set(x_66, 0, x_163);
x_165 = l_Lean_MessageData_ofExpr(x_160);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_66);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_indentD(x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_168, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
return x_172;
}
else
{
lean_dec(x_160);
lean_dec_ref(x_72);
lean_free_object(x_66);
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = lean_box(0);
goto block_64;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_174 = x_159;
} else {
 lean_dec_ref(x_159);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = lean_ctor_get(x_157, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_177 = x_157;
} else {
 lean_dec_ref(x_157);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
}
}
else
{
uint8_t x_179; 
lean_dec_ref(x_72);
lean_free_object(x_66);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_128);
if (x_179 == 0)
{
return x_128;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_128, 0);
lean_inc(x_180);
lean_dec(x_128);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_66, 0);
x_183 = lean_ctor_get(x_66, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_66);
x_184 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(x_182, x_4);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Expr_cleanupAnnotations(x_185);
if (lean_obj_tag(x_186) == 7)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_186, 2);
lean_inc_ref(x_189);
x_190 = lean_ctor_get_uint8(x_186, sizeof(void*)*3 + 8);
lean_dec_ref(x_186);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_188);
x_191 = l_Lean_Meta_getLevel(x_188, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
lean_inc_ref(x_189);
lean_inc_ref(x_188);
lean_inc(x_187);
x_193 = l_Lean_Expr_lam___override(x_187, x_188, x_189, x_190);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_221; 
lean_dec(x_187);
x_221 = lean_ctor_get(x_2, 0);
lean_inc(x_221);
lean_dec_ref(x_2);
x_194 = x_221;
x_195 = x_3;
x_196 = x_4;
x_197 = x_5;
x_198 = x_6;
x_199 = lean_box(0);
goto block_220;
}
else
{
lean_object* x_222; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_222 = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(x_187, x_3, x_5, x_6);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_194 = x_223;
x_195 = x_3;
x_196 = x_4;
x_197 = x_5;
x_198 = x_6;
x_199 = lean_box(0);
goto block_220;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec_ref(x_193);
lean_dec(x_192);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_183);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_224);
return x_226;
}
}
block_220:
{
uint8_t x_200; lean_object* x_201; 
x_200 = 0;
lean_inc(x_196);
lean_inc_ref(x_188);
x_201 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(x_189, x_183, x_194, x_190, x_188, x_200, x_195, x_196, x_197, x_198);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_207 = x_203;
} else {
 lean_dec_ref(x_203);
 x_207 = lean_box(0);
}
x_208 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5;
x_209 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_207;
 lean_ctor_set_tag(x_210, 1);
}
lean_ctor_set(x_210, 0, x_192);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_mkConst(x_208, x_210);
x_212 = l_Lean_mkApp4(x_211, x_188, x_193, x_204, x_205);
x_213 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(x_1, x_212, x_196);
lean_dec(x_196);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_214 = x_213;
} else {
 lean_dec_ref(x_213);
 x_214 = lean_box(0);
}
x_215 = l_Lean_Expr_mvarId_x21(x_206);
lean_dec(x_206);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_196);
lean_dec_ref(x_193);
lean_dec(x_192);
lean_dec_ref(x_188);
lean_dec(x_1);
x_217 = lean_ctor_get(x_201, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_218 = x_201;
} else {
 lean_dec_ref(x_201);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_217);
return x_219;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_183);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_191, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_228 = x_191;
} else {
 lean_dec_ref(x_191);
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
lean_object* x_230; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_186);
lean_inc(x_1);
x_230 = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(x_1, x_186, x_183, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
if (lean_obj_tag(x_231) == 1)
{
lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_186);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
lean_dec_ref(x_231);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 1, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_233);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_232);
lean_dec(x_231);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_186);
x_235 = lean_infer_type(x_186, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_237 = l_Lean_Meta_whnfD(x_236, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = l_Lean_Expr_isForall(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_2);
lean_dec(x_1);
x_240 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7;
x_241 = l_Lean_MessageData_ofExpr(x_186);
x_242 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9;
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_MessageData_ofExpr(x_238);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Lean_indentD(x_245);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_247, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
else
{
lean_dec(x_238);
lean_dec_ref(x_186);
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = lean_box(0);
goto block_64;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec_ref(x_186);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_ctor_get(x_237, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_253 = x_237;
} else {
 lean_dec_ref(x_237);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_186);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_235, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_256 = x_235;
} else {
 lean_dec_ref(x_235);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_255);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec_ref(x_186);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_230, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_259 = x_230;
} else {
 lean_dec_ref(x_230);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_65);
if (x_261 == 0)
{
return x_65;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_65, 0);
lean_inc(x_262);
lean_dec(x_65);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
lean_inc_ref(x_13);
lean_inc(x_9);
lean_inc_ref(x_10);
x_17 = l_Lean_Meta_introNCore(x_14, x_16, x_15, x_11, x_11, x_10, x_9, x_13, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Tactic_Conv_markAsConvGoal(x_19, x_10, x_9, x_13, x_12);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1;
x_31 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(x_30, x_25, x_26, x_27, x_28);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
return x_31;
}
block_64:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3;
lean_inc_ref(x_35);
x_39 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_38, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = 0;
x_42 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2;
x_43 = lean_box(0);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
x_44 = l_Lean_MVarId_apply(x_1, x_40, x_42, x_43, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
if (lean_obj_tag(x_46) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec_ref(x_2);
x_51 = lean_box(0);
lean_ctor_set(x_45, 1, x_51);
lean_ctor_set(x_45, 0, x_50);
x_8 = lean_box(0);
x_9 = x_34;
x_10 = x_33;
x_11 = x_41;
x_12 = x_36;
x_13 = x_35;
x_14 = x_48;
x_15 = x_45;
goto block_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
lean_dec_ref(x_2);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_8 = lean_box(0);
x_9 = x_34;
x_10 = x_33;
x_11 = x_41;
x_12 = x_36;
x_13 = x_35;
x_14 = x_52;
x_15 = x_55;
goto block_24;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
lean_dec_ref(x_45);
x_57 = lean_box(0);
x_8 = lean_box(0);
x_9 = x_34;
x_10 = x_33;
x_11 = x_41;
x_12 = x_36;
x_13 = x_35;
x_14 = x_56;
x_15 = x_57;
goto block_24;
}
}
else
{
lean_dec_ref(x_45);
lean_dec(x_2);
x_25 = x_33;
x_26 = x_34;
x_27 = x_35;
x_28 = x_36;
x_29 = lean_box(0);
goto block_32;
}
}
else
{
lean_dec(x_45);
lean_dec(x_2);
x_25 = x_33;
x_26 = x_34;
x_27 = x_35;
x_28 = x_36;
x_29 = lean_box(0);
goto block_32;
}
}
else
{
uint8_t x_58; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_39);
if (x_61 == 0)
{
return x_39;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_39, 0);
lean_inc(x_62);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(x_9, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(x_1, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binderIdent", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_39; uint8_t x_40; 
x_14 = lean_array_uget(x_2, x_4);
x_39 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1;
lean_inc(x_14);
x_40 = l_Lean_Syntax_isOfKind(x_14, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_15 = x_41;
goto block_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Syntax_getArg(x_14, x_42);
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3;
lean_inc(x_43);
x_45 = l_Lean_Syntax_isOfKind(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = lean_box(0);
x_15 = x_46;
goto block_38;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_TSyntax_getId(x_43);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_15 = x_48;
goto block_38;
}
}
block_38:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get(x_9, 11);
x_28 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_29 = lean_ctor_get(x_9, 12);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_31 = lean_ctor_get(x_9, 13);
x_32 = l_Lean_replaceRef(x_14, x_21);
lean_dec(x_14);
lean_inc_ref(x_31);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc_ref(x_17);
lean_inc_ref(x_16);
x_33 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_19);
lean_ctor_set(x_33, 4, x_20);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_22);
lean_ctor_set(x_33, 7, x_23);
lean_ctor_set(x_33, 8, x_24);
lean_ctor_set(x_33, 9, x_25);
lean_ctor_set(x_33, 10, x_26);
lean_ctor_set(x_33, 11, x_27);
lean_ctor_set(x_33, 12, x_29);
lean_ctor_set(x_33, 13, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*14, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*14 + 1, x_30);
lean_inc(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
x_34 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(x_15, x_6, x_7, x_8, x_33, x_10);
if (lean_obj_tag(x_34) == 0)
{
size_t x_35; size_t x_36; 
lean_dec_ref(x_34);
x_35 = 1;
x_36 = lean_usize_add(x_4, x_35);
{
size_t _tmp_3 = x_36;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = l_Array_isEmpty___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_array_size(x_13);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(x_15, x_13, x_16, x_17, x_15, x_3, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
}
else
{
return x_18;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_13);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(x_22, x_3, x_6, x_7, x_8, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalExt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExt", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0;
x_4 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(207u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_unsigned_to_nat(213u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(207u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(207u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (x_1 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 5);
x_22 = l_Lean_replaceRef(x_3, x_21);
lean_dec(x_21);
lean_inc(x_22);
lean_ctor_set(x_16, 5, x_22);
x_23 = l_Lean_Syntax_getArg(x_3, x_4);
x_24 = l_Lean_Elab_Tactic_Conv_elabArg___closed__4;
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_25 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_24);
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0;
lean_inc_ref(x_5);
x_28 = l_Lean_Name_mkStr2(x_5, x_27);
lean_inc(x_23);
x_29 = l_Lean_Syntax_isOfKind(x_23, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Lean_SourceInfo_fromRef(x_22, x_26);
lean_dec(x_22);
x_32 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
x_33 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_32);
lean_inc(x_31);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_inc(x_31);
x_35 = l_Lean_Syntax_node1(x_31, x_9, x_23);
x_36 = l_Lean_Syntax_node2(x_31, x_33, x_34, x_35);
x_37 = l_Lean_Elab_Tactic_evalTactic(x_36, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
x_38 = 0;
x_39 = l_Lean_SourceInfo_fromRef(x_22, x_38);
lean_dec(x_22);
x_40 = l_Lean_Elab_Tactic_Conv_elabArg___closed__0;
x_41 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_40);
lean_inc(x_39);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Syntax_node2(x_39, x_41, x_42, x_23);
x_44 = l_Lean_Elab_Tactic_evalTactic(x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
x_47 = lean_ctor_get(x_16, 2);
x_48 = lean_ctor_get(x_16, 3);
x_49 = lean_ctor_get(x_16, 4);
x_50 = lean_ctor_get(x_16, 5);
x_51 = lean_ctor_get(x_16, 6);
x_52 = lean_ctor_get(x_16, 7);
x_53 = lean_ctor_get(x_16, 8);
x_54 = lean_ctor_get(x_16, 9);
x_55 = lean_ctor_get(x_16, 10);
x_56 = lean_ctor_get(x_16, 11);
x_57 = lean_ctor_get_uint8(x_16, sizeof(void*)*14);
x_58 = lean_ctor_get(x_16, 12);
x_59 = lean_ctor_get_uint8(x_16, sizeof(void*)*14 + 1);
x_60 = lean_ctor_get(x_16, 13);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_61 = l_Lean_replaceRef(x_3, x_50);
lean_dec(x_50);
lean_inc(x_61);
x_62 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_46);
lean_ctor_set(x_62, 2, x_47);
lean_ctor_set(x_62, 3, x_48);
lean_ctor_set(x_62, 4, x_49);
lean_ctor_set(x_62, 5, x_61);
lean_ctor_set(x_62, 6, x_51);
lean_ctor_set(x_62, 7, x_52);
lean_ctor_set(x_62, 8, x_53);
lean_ctor_set(x_62, 9, x_54);
lean_ctor_set(x_62, 10, x_55);
lean_ctor_set(x_62, 11, x_56);
lean_ctor_set(x_62, 12, x_58);
lean_ctor_set(x_62, 13, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*14, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*14 + 1, x_59);
x_63 = l_Lean_Syntax_getArg(x_3, x_4);
x_64 = l_Lean_Elab_Tactic_Conv_elabArg___closed__4;
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_65 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_64);
lean_inc(x_63);
x_66 = l_Lean_Syntax_isOfKind(x_63, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0;
lean_inc_ref(x_5);
x_68 = l_Lean_Name_mkStr2(x_5, x_67);
lean_inc(x_63);
x_69 = l_Lean_Syntax_isOfKind(x_63, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = l_Lean_SourceInfo_fromRef(x_61, x_66);
lean_dec(x_61);
x_72 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0;
x_73 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_72);
lean_inc(x_71);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
lean_inc(x_71);
x_75 = l_Lean_Syntax_node1(x_71, x_9, x_63);
x_76 = l_Lean_Syntax_node2(x_71, x_73, x_74, x_75);
x_77 = l_Lean_Elab_Tactic_evalTactic(x_76, x_10, x_11, x_12, x_13, x_14, x_15, x_62, x_17);
return x_77;
}
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_9);
x_78 = 0;
x_79 = l_Lean_SourceInfo_fromRef(x_61, x_78);
lean_dec(x_61);
x_80 = l_Lean_Elab_Tactic_Conv_elabArg___closed__0;
x_81 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_8, x_80);
lean_inc(x_79);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Syntax_node2(x_79, x_81, x_82, x_63);
x_84 = l_Lean_Elab_Tactic_evalTactic(x_83, x_10, x_11, x_12, x_13, x_14, x_15, x_62, x_17);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object** _args) {
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
x_19 = lean_unbox(x_1);
x_20 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0;
x_4 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
x_11 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2;
lean_ctor_set(x_8, 2, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
lean_ctor_set(x_6, 7, x_18);
x_19 = lean_st_ref_set(x_1, x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_6, 7);
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
x_24 = lean_ctor_get(x_6, 2);
x_25 = lean_ctor_get(x_6, 3);
x_26 = lean_ctor_get(x_6, 4);
x_27 = lean_ctor_get(x_6, 5);
x_28 = lean_ctor_get(x_6, 6);
x_29 = lean_ctor_get(x_6, 8);
lean_inc(x_29);
lean_inc(x_21);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_30);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set(x_36, 4, x_26);
lean_ctor_set(x_36, 5, x_27);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_29);
x_37 = lean_st_ref_set(x_1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
lean_inc(x_1);
x_16 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_st_ref_take(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 2);
lean_dec(x_23);
x_24 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
lean_ctor_set(x_21, 2, x_24);
x_25 = lean_st_ref_set(x_1, x_19);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_27);
lean_ctor_set(x_19, 7, x_31);
x_32 = lean_st_ref_set(x_1, x_19);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_19, 7);
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_ctor_get(x_19, 2);
x_38 = lean_ctor_get(x_19, 3);
x_39 = lean_ctor_get(x_19, 4);
x_40 = lean_ctor_get(x_19, 5);
x_41 = lean_ctor_get(x_19, 6);
x_42 = lean_ctor_get(x_19, 8);
lean_inc(x_42);
lean_inc(x_34);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_43 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_44 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_45);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_46 = x_34;
} else {
 lean_dec_ref(x_34);
 x_46 = lean_box(0);
}
x_47 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 3, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_43);
x_49 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_38);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
lean_ctor_set(x_49, 7, x_48);
lean_ctor_set(x_49, 8, x_42);
x_50 = lean_st_ref_set(x_1, x_49);
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_16, 0, x_51);
return x_16;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_52 = lean_ctor_get(x_16, 0);
lean_inc(x_52);
lean_dec(x_16);
x_53 = lean_st_ref_take(x_1);
x_54 = lean_ctor_get(x_53, 7);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_53, 4);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_53, 5);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_53, 6);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_53, 8);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 lean_ctor_release(x_53, 7);
 lean_ctor_release(x_53, 8);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get_uint8(x_54, sizeof(void*)*3);
x_65 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
x_68 = l_Lean_PersistentArray_push___redArg(x_10, x_52);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 3, 1);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_64);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 9, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_57);
lean_ctor_set(x_70, 3, x_58);
lean_ctor_set(x_70, 4, x_59);
lean_ctor_set(x_70, 5, x_60);
lean_ctor_set(x_70, 6, x_61);
lean_ctor_set(x_70, 7, x_69);
lean_ctor_set(x_70, 8, x_62);
x_71 = lean_st_ref_set(x_1, x_70);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_10);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
return x_16;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_16, 0);
lean_inc(x_75);
lean_dec(x_16);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_st_ref_get(x_10);
x_13 = lean_ctor_get(x_12, 7);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec_ref(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_2);
x_15 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_ctor_set_tag(x_18, 1);
x_21 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_18);
lean_dec_ref(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_20);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_29);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_31 = x_30;
} else {
 lean_dec_ref(x_30);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec_ref(x_18);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; 
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enterArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_9, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_22 = lean_nat_mul(x_2, x_9);
lean_inc(x_3);
x_23 = lean_array_get_borrowed(x_3, x_4, x_22);
x_50 = lean_nat_add(x_22, x_8);
lean_dec(x_22);
x_51 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
x_53 = lean_box(0);
x_24 = x_53;
goto block_49;
}
else
{
lean_object* x_54; 
x_54 = lean_array_fget_borrowed(x_4, x_50);
lean_dec(x_50);
lean_inc(x_54);
x_24 = x_54;
goto block_49;
}
block_49:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0;
lean_inc(x_23);
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_array_push(x_26, x_24);
x_28 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2;
x_29 = lean_box(2);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
x_31 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_30, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_34 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_35 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_36 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_37 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4;
lean_inc(x_23);
x_38 = l_Lean_Syntax_isOfKind(x_23, x_37);
x_39 = lean_box(x_38);
lean_inc(x_6);
lean_inc(x_23);
x_40 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 18, 9);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_5);
lean_closure_set(x_40, 2, x_23);
lean_closure_set(x_40, 3, x_6);
lean_closure_set(x_40, 4, x_33);
lean_closure_set(x_40, 5, x_34);
lean_closure_set(x_40, 6, x_35);
lean_closure_set(x_40, 7, x_36);
lean_closure_set(x_40, 8, x_28);
x_41 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 11, 1);
lean_closure_set(x_41, 0, x_32);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_42 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(x_40, x_41, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_9, x_43);
lean_dec(x_9);
{
lean_object* _tmp_8 = x_44;
lean_object* _tmp_9 = x_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
return x_42;
}
}
else
{
uint8_t x_46; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalEnter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed), 10, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0;
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_14);
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2;
x_20 = lean_box(2);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
x_22 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed), 11, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Tactic_Conv_evalEnter___closed__0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(x_26, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_27);
x_28 = lean_box(0);
x_29 = l_Lean_Syntax_getArg(x_1, x_15);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_add(x_31, x_13);
x_33 = lean_nat_shiftr(x_32, x_13);
lean_dec(x_32);
x_34 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(x_33, x_15, x_28, x_30, x_25, x_11, x_25, x_13, x_11, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_30);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_25);
return x_34;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_25);
return x_37;
}
}
else
{
return x_34;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_27;
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalEnter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; 
x_23 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_12, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
lean_object* x_23; 
x_23 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enter", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalEnter", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2;
x_2 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2;
x_4 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6;
x_5 = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1;
x_4 = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4);
l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0 = _init_l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__2);
l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1);
l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3);
l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0 = _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0);
l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__2___redArg___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5);
l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1);
l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__2);
l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__3);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5);
l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6 = _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__6);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___closed__0();
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4);
l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5 = _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
l_Lean_Elab_Tactic_Conv_elabArg___closed__0 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__0);
l_Lean_Elab_Tactic_Conv_elabArg___closed__1 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__1);
l_Lean_Elab_Tactic_Conv_elabArg___closed__2 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__2);
l_Lean_Elab_Tactic_Conv_elabArg___closed__3 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__3);
l_Lean_Elab_Tactic_Conv_elabArg___closed__4 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__4);
l_Lean_Elab_Tactic_Conv_elabArg___closed__5 = _init_l_Lean_Elab_Tactic_Conv_elabArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___closed__5);
l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0);
l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0);
l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1);
l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0);
l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0);
l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1);
l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2);
l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3 = _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0 = _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8);
l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9 = _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5);
l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__2);
l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2);
l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3);
l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4 = _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__4);
l_Lean_Elab_Tactic_Conv_evalEnter___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalEnter___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0);
l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0 = _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0);
l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
