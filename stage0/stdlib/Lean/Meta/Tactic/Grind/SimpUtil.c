// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.List Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__12;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__7;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__4;
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__24;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__28;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__40;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__9;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__7;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__6;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__37;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__31;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__32;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__21;
static lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0;
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__6;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__8;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__11;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__7;
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__14;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__56;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__20;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__11;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__48;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__57;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__1;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__8;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__53;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__18;
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__0;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__10;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__16;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__25;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__20;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__45;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__60;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__64;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__29;
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__12;
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__25;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__5;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__55;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__0;
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__9;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__43;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__49;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__4;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__36;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_(lean_object*);
static lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__7;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__46;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__19;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__22;
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__41;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__10;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__34;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__47;
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__10;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__18;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__3;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__15;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__61;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__26;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__11;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__10;
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__18;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__17;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__0;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__17;
lean_object* l_Lean_mkIntLit(lean_object*);
static uint64_t l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__17;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__21;
lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__44;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__42;
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__38;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__8;
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__23;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__28;
static lean_object* l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__8;
lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__39;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__59;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__9;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__19;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__7;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__2;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__15;
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__58;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__19;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__13;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__27;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__54;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__23;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__20;
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__26;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__50;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__13;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__62;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__27;
static lean_object* l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__14;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__13;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__30;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__35;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__16;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__33;
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__63;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__22;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__16;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__0;
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__51;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__52;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__14;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___reduceCtorEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
static lean_object* l_Lean_Meta_Grind_getSimpContext___closed__6;
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("normExt", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_mkSimpExt(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = 0;
x_16 = 0;
x_17 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_addSimpTheorem(x_1, x_14, x_15, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
{
size_t _tmp_4 = x_21;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_19;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = 0;
x_16 = 0;
x_17 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_addSimpTheorem(x_1, x_14, x_12, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
{
size_t _tmp_4 = x_21;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_19;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_normExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` normalization theorems have already been initialized", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_registerNormTheorems___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
x_9 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_8, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_12);
lean_dec_ref(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_Grind_registerNormTheorems___closed__2;
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_1);
x_18 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_8, x_16, x_1, x_17, x_18, x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_array_size(x_2);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_8, x_16, x_2, x_21, x_18, x_16, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
return x_22;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_registerNormTheorems_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_isEmpty___at___Lean_Meta_Grind_registerNormTheorems_spec__2(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_registerNormTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
x_13 = lean_name_eq(x_1, x_12);
x_2 = x_13;
goto block_9;
}
else
{
x_2 = x_11;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
x_4 = lean_name_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
x_8 = lean_name_eq(x_1, x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bool_eq_to_prop", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__7;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__16;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_eq", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__19;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_self", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__22;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("flip_bool_eq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__24;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__25;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpEq___redArg___closed__27;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
if (x_25 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
lean_dec(x_10);
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_22, x_3, x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_33 = l_Lean_Expr_cleanupAnnotations(x_27);
x_34 = l_Lean_Meta_Grind_simpEq___redArg___closed__3;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_expr_eqv(x_19, x_16);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_62 = l_Lean_Meta_Grind_simpEq___redArg___closed__12;
x_63 = lean_expr_eqv(x_16, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Meta_Grind_simpEq___redArg___closed__15;
x_65 = lean_expr_eqv(x_16, x_64);
lean_dec_ref(x_16);
if (x_65 == 0)
{
lean_dec_ref(x_19);
goto block_32;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_29);
lean_inc_ref(x_19);
x_66 = l_Lean_mkNot(x_19);
x_67 = l_Lean_Meta_Grind_simpEq___redArg___closed__18;
x_68 = l_Lean_Expr_app___override(x_67, x_19);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_25);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_28);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_29);
lean_dec_ref(x_16);
x_73 = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
lean_inc_ref(x_19);
x_74 = l_Lean_Expr_app___override(x_73, x_19);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_19);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_25);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_28);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_29);
lean_dec_ref(x_16);
x_79 = l_Lean_Expr_constLevels_x21(x_23);
lean_dec_ref(x_23);
x_80 = l_Lean_Meta_Grind_simpEq___redArg___closed__12;
x_81 = l_Lean_Meta_Grind_simpEq___redArg___closed__23;
x_82 = l_Lean_Expr_const___override(x_81, x_79);
x_83 = l_Lean_mkAppB(x_82, x_22, x_19);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_25);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_28);
return x_87;
}
}
else
{
lean_object* x_88; 
x_88 = l_Lean_Expr_getAppFn(x_16);
if (lean_obj_tag(x_88) == 4)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_102; lean_object* x_114; uint8_t x_115; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_114 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_115 = lean_name_eq(x_89, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_117 = lean_name_eq(x_89, x_116);
x_102 = x_117;
goto block_113;
}
else
{
x_102 = x_115;
goto block_113;
}
block_101:
{
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_90);
lean_dec(x_90);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(x_89);
lean_dec(x_89);
x_36 = x_93;
goto block_60;
}
else
{
lean_dec(x_89);
x_36 = x_92;
goto block_60;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_29);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_inc_ref(x_19);
lean_inc_ref(x_16);
x_94 = l_Lean_mkApp3(x_23, x_22, x_16, x_19);
x_95 = l_Lean_Meta_Grind_simpEq___redArg___closed__26;
x_96 = l_Lean_mkAppB(x_95, x_19, x_16);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_35);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_28);
return x_100;
}
}
block_113:
{
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Lean_Expr_getAppFn(x_19);
if (lean_obj_tag(x_103) == 4)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_106 = lean_name_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_108 = lean_name_eq(x_104, x_107);
x_90 = x_104;
x_91 = x_108;
goto block_101;
}
else
{
x_90 = x_104;
x_91 = x_106;
goto block_101;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_103);
lean_dec(x_89);
lean_dec(x_29);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_109 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_28);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_89);
lean_dec(x_29);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_111 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_28);
return x_112;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_88);
lean_dec(x_29);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_118 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_28);
return x_119;
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
block_60:
{
if (x_36 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = l_Lean_Meta_Grind_simpEq___redArg___closed__6;
lean_inc_ref(x_19);
lean_inc_ref(x_22);
lean_inc_ref(x_23);
x_38 = l_Lean_mkApp3(x_23, x_22, x_19, x_37);
lean_inc_ref(x_16);
x_39 = l_Lean_mkApp3(x_23, x_22, x_16, x_37);
x_40 = l_Lean_Meta_mkEq(x_38, x_39, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Meta_Grind_simpEq___redArg___closed__9;
x_44 = l_Lean_mkAppB(x_43, x_19, x_16);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_35);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = l_Lean_Meta_Grind_simpEq___redArg___closed__9;
x_51 = l_Lean_mkAppB(x_50, x_19, x_16);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_35);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
x_56 = !lean_is_exclusive(x_40);
if (x_56 == 0)
{
return x_40;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_40, 0);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpEq", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpEq___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpDIte___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpDIte___redArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_eq_ite", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpDIte___redArg___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
x_4 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_11 = l_Lean_Expr_cleanupAnnotations(x_5);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_16) == 6)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_16);
x_30 = l_Lean_Expr_hasLooseBVars(x_29);
if (x_30 == 0)
{
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_13);
x_32 = l_Lean_Expr_hasLooseBVars(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = l_Lean_Expr_constLevels_x21(x_26);
lean_dec_ref(x_26);
x_34 = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
lean_inc(x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_33);
lean_inc_ref(x_31);
lean_inc_ref(x_29);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
lean_inc_ref(x_25);
x_36 = l_Lean_mkApp5(x_35, x_25, x_22, x_19, x_29, x_31);
x_37 = l_Lean_Meta_Grind_simpDIte___redArg___closed__5;
x_38 = l_Lean_Expr_const___override(x_37, x_33);
x_39 = l_Lean_mkApp5(x_38, x_22, x_25, x_29, x_31, x_19);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_28);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
x_44 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_46 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_48 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
x_50 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
}
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 2, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpDIte___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_simpDIte___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpDIte", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpDIte___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exists", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_forall", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__4;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_implies", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__6;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Or", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__14;
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__16;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__19;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__21;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__23;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__25;
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__21;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__26;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__25;
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__29;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_eq_true", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__32;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__33;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_eq_false", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__35;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__36;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_eq_prop", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__38;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__39;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_and", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__42;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__43;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_or", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__46;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__47;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__49;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_exists", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__52;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_not", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__54;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__55;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_true", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__57;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__58;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__59;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__61() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_false", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__61;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__62;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNot___redArg___closed__63;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Meta_Grind_pushNot___redArg___closed__1;
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
lean_dec_ref(x_17);
if (x_19 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_13;
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_10);
x_101 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_3, x_9);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
x_105 = l_Lean_Expr_cleanupAnnotations(x_103);
x_106 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_107 = l_Lean_Expr_isConstOf(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_109 = l_Lean_Expr_isConstOf(x_105, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Expr_isApp(x_105);
if (x_110 == 0)
{
lean_dec_ref(x_105);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc_ref(x_111);
x_112 = l_Lean_Expr_appFnCleanup___redArg(x_105);
x_113 = l_Lean_Expr_isConstOf(x_112, x_18);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_Expr_isApp(x_112);
if (x_114 == 0)
{
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_115);
x_116 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_117 = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
x_118 = l_Lean_Expr_isConstOf(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_120 = l_Lean_Expr_isConstOf(x_116, x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
x_122 = l_Lean_Expr_isConstOf(x_116, x_121);
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = l_Lean_Expr_isApp(x_116);
if (x_123 == 0)
{
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_111);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_124);
x_125 = l_Lean_Expr_appFnCleanup___redArg(x_116);
x_126 = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
x_127 = l_Lean_Expr_isConstOf(x_125, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_isApp(x_125);
if (x_128 == 0)
{
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_115);
lean_dec_ref(x_111);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_129);
x_130 = l_Lean_Expr_appFnCleanup___redArg(x_125);
x_131 = l_Lean_Meta_Grind_pushNot___redArg___closed__15;
x_132 = l_Lean_Expr_isConstOf(x_130, x_131);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = l_Lean_Expr_isApp(x_130);
if (x_133 == 0)
{
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_124);
lean_dec_ref(x_115);
lean_dec_ref(x_111);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_134);
x_135 = l_Lean_Expr_appFnCleanup___redArg(x_130);
x_136 = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
x_137 = l_Lean_Expr_isConstOf(x_135, x_136);
if (x_137 == 0)
{
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_129);
lean_dec_ref(x_124);
lean_dec_ref(x_115);
lean_dec_ref(x_111);
lean_free_object(x_101);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_104;
goto block_100;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc_ref(x_115);
x_138 = l_Lean_mkNot(x_115);
lean_inc_ref(x_111);
x_139 = l_Lean_mkNot(x_111);
lean_inc_ref(x_124);
lean_inc_ref(x_129);
x_140 = l_Lean_mkApp5(x_135, x_134, x_129, x_124, x_138, x_139);
x_141 = l_Lean_Meta_Grind_pushNot___redArg___closed__18;
x_142 = l_Lean_mkApp4(x_141, x_129, x_124, x_115, x_111);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_137);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_101, 0, x_145);
return x_101;
}
}
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec_ref(x_130);
lean_dec_ref(x_124);
lean_free_object(x_101);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_146 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_129, x_3, x_104);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = l_Lean_Expr_cleanupAnnotations(x_148);
x_150 = l_Lean_Meta_Grind_pushNot___redArg___closed__20;
x_151 = l_Lean_Expr_isConstOf(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_Meta_Grind_pushNot___redArg___closed__22;
x_153 = l_Lean_Expr_isConstOf(x_149, x_152);
lean_dec_ref(x_149);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec_ref(x_115);
lean_dec_ref(x_111);
x_154 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_146, 0, x_154);
return x_146;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = l_Lean_Meta_Grind_pushNot___redArg___closed__24;
lean_inc_ref(x_111);
x_156 = l_Lean_mkIntAdd(x_111, x_155);
lean_inc_ref(x_115);
x_157 = l_Lean_mkIntLE(x_156, x_115);
x_158 = l_Lean_Meta_Grind_pushNot___redArg___closed__27;
x_159 = l_Lean_mkAppB(x_158, x_115, x_111);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_153);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_146, 0, x_162);
return x_146;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_149);
x_163 = l_Lean_Meta_Grind_pushNot___redArg___closed__28;
lean_inc_ref(x_111);
x_164 = l_Lean_mkNatAdd(x_111, x_163);
lean_inc_ref(x_115);
x_165 = l_Lean_mkNatLE(x_164, x_115);
x_166 = l_Lean_Meta_Grind_pushNot___redArg___closed__30;
x_167 = l_Lean_mkAppB(x_166, x_115, x_111);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_151);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_146, 0, x_170);
return x_146;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_146, 0);
x_172 = lean_ctor_get(x_146, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_146);
x_173 = l_Lean_Expr_cleanupAnnotations(x_171);
x_174 = l_Lean_Meta_Grind_pushNot___redArg___closed__20;
x_175 = l_Lean_Expr_isConstOf(x_173, x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = l_Lean_Meta_Grind_pushNot___redArg___closed__22;
x_177 = l_Lean_Expr_isConstOf(x_173, x_176);
lean_dec_ref(x_173);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_115);
lean_dec_ref(x_111);
x_178 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_172);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_180 = l_Lean_Meta_Grind_pushNot___redArg___closed__24;
lean_inc_ref(x_111);
x_181 = l_Lean_mkIntAdd(x_111, x_180);
lean_inc_ref(x_115);
x_182 = l_Lean_mkIntLE(x_181, x_115);
x_183 = l_Lean_Meta_Grind_pushNot___redArg___closed__27;
x_184 = l_Lean_mkAppB(x_183, x_115, x_111);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_177);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_172);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_173);
x_189 = l_Lean_Meta_Grind_pushNot___redArg___closed__28;
lean_inc_ref(x_111);
x_190 = l_Lean_mkNatAdd(x_111, x_189);
lean_inc_ref(x_115);
x_191 = l_Lean_mkNatLE(x_190, x_115);
x_192 = l_Lean_Meta_Grind_pushNot___redArg___closed__30;
x_193 = l_Lean_mkAppB(x_192, x_115, x_111);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*2, x_175);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_172);
return x_197;
}
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_198 = l_Lean_Expr_isProp(x_124);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
lean_free_object(x_101);
x_199 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_111, x_3, x_104);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = l_Lean_Expr_cleanupAnnotations(x_201);
x_203 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_204 = l_Lean_Expr_isConstOf(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_206 = l_Lean_Expr_isConstOf(x_202, x_205);
lean_dec_ref(x_202);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_115);
x_207 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_199, 0, x_207);
return x_199;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = l_Lean_Meta_Grind_pushNot___redArg___closed__31;
lean_inc_ref(x_115);
x_209 = l_Lean_mkApp3(x_125, x_124, x_115, x_208);
x_210 = l_Lean_Meta_Grind_pushNot___redArg___closed__34;
x_211 = l_Lean_Expr_app___override(x_210, x_115);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*2, x_127);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_199, 0, x_214);
return x_199;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_202);
x_215 = l_Lean_Meta_Grind_simpEq___redArg___closed__6;
lean_inc_ref(x_115);
x_216 = l_Lean_mkApp3(x_125, x_124, x_115, x_215);
x_217 = l_Lean_Meta_Grind_pushNot___redArg___closed__37;
x_218 = l_Lean_Expr_app___override(x_217, x_115);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*2, x_127);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_199, 0, x_221);
return x_199;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_224 = l_Lean_Expr_cleanupAnnotations(x_222);
x_225 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_226 = l_Lean_Expr_isConstOf(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_228 = l_Lean_Expr_isConstOf(x_224, x_227);
lean_dec_ref(x_224);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_115);
x_229 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_223);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_231 = l_Lean_Meta_Grind_pushNot___redArg___closed__31;
lean_inc_ref(x_115);
x_232 = l_Lean_mkApp3(x_125, x_124, x_115, x_231);
x_233 = l_Lean_Meta_Grind_pushNot___redArg___closed__34;
x_234 = l_Lean_Expr_app___override(x_233, x_115);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_127);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_223);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_224);
x_239 = l_Lean_Meta_Grind_simpEq___redArg___closed__6;
lean_inc_ref(x_115);
x_240 = l_Lean_mkApp3(x_125, x_124, x_115, x_239);
x_241 = l_Lean_Meta_Grind_pushNot___redArg___closed__37;
x_242 = l_Lean_Expr_app___override(x_241, x_115);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
x_244 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set_uint8(x_244, sizeof(void*)*2, x_127);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_223);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_3);
lean_inc_ref(x_111);
x_247 = l_Lean_mkNot(x_111);
lean_inc_ref(x_115);
x_248 = l_Lean_mkApp3(x_125, x_124, x_115, x_247);
x_249 = l_Lean_Meta_Grind_pushNot___redArg___closed__40;
x_250 = l_Lean_mkAppB(x_249, x_115, x_111);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_252, 0, x_248);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set_uint8(x_252, sizeof(void*)*2, x_127);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_101, 0, x_253);
return x_101;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec_ref(x_116);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_254 = l_Lean_Meta_Grind_pushNot___redArg___closed__41;
lean_inc_ref(x_115);
x_255 = l_Lean_mkNot(x_115);
lean_inc_ref(x_111);
x_256 = l_Lean_mkNot(x_111);
x_257 = l_Lean_mkAppB(x_254, x_255, x_256);
x_258 = l_Lean_Meta_Grind_pushNot___redArg___closed__44;
x_259 = l_Lean_mkAppB(x_258, x_115, x_111);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_261, 0, x_257);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_122);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_101, 0, x_262);
return x_101;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec_ref(x_116);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_263 = l_Lean_Meta_Grind_pushNot___redArg___closed__45;
lean_inc_ref(x_115);
x_264 = l_Lean_mkNot(x_115);
lean_inc_ref(x_111);
x_265 = l_Lean_mkNot(x_111);
x_266 = l_Lean_mkAppB(x_263, x_264, x_265);
x_267 = l_Lean_Meta_Grind_pushNot___redArg___closed__48;
x_268 = l_Lean_mkAppB(x_267, x_115, x_111);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set_uint8(x_270, sizeof(void*)*2, x_120);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_101, 0, x_271);
return x_101;
}
}
else
{
lean_object* x_272; 
lean_dec_ref(x_116);
lean_free_object(x_101);
lean_dec_ref(x_1);
lean_inc_ref(x_115);
x_272 = l_Lean_Meta_getLevel(x_115, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = l_Lean_Meta_Grind_pushNot___redArg___closed__50;
x_276 = 0;
x_277 = l_Lean_Meta_Grind_pushNot___redArg___closed__51;
lean_inc_ref(x_111);
x_278 = l_Lean_Expr_app___override(x_111, x_277);
x_279 = l_Lean_mkNot(x_278);
lean_inc_ref(x_115);
x_280 = l_Lean_Expr_forallE___override(x_275, x_115, x_279, x_276);
x_281 = l_Lean_Meta_Grind_pushNot___redArg___closed__53;
x_282 = lean_box(0);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_274);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_Expr_const___override(x_281, x_283);
x_285 = l_Lean_mkAppB(x_284, x_115, x_111);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_287, 0, x_280);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_118);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_272, 0, x_288);
return x_272;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_289 = lean_ctor_get(x_272, 0);
x_290 = lean_ctor_get(x_272, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_272);
x_291 = l_Lean_Meta_Grind_pushNot___redArg___closed__50;
x_292 = 0;
x_293 = l_Lean_Meta_Grind_pushNot___redArg___closed__51;
lean_inc_ref(x_111);
x_294 = l_Lean_Expr_app___override(x_111, x_293);
x_295 = l_Lean_mkNot(x_294);
lean_inc_ref(x_115);
x_296 = l_Lean_Expr_forallE___override(x_291, x_115, x_295, x_292);
x_297 = l_Lean_Meta_Grind_pushNot___redArg___closed__53;
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_289);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lean_Expr_const___override(x_297, x_299);
x_301 = l_Lean_mkAppB(x_300, x_115, x_111);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_303, 0, x_296);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_118);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_290);
return x_305;
}
}
else
{
uint8_t x_306; 
lean_dec_ref(x_115);
lean_dec_ref(x_111);
x_306 = !lean_is_exclusive(x_272);
if (x_306 == 0)
{
return x_272;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_272, 0);
x_308 = lean_ctor_get(x_272, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_272);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec_ref(x_112);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_310 = l_Lean_Meta_Grind_pushNot___redArg___closed__56;
lean_inc_ref(x_111);
x_311 = l_Lean_Expr_app___override(x_310, x_111);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_313 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_313, 0, x_111);
lean_ctor_set(x_313, 1, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*2, x_113);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_101, 0, x_314);
return x_101;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec_ref(x_105);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_315 = l_Lean_Meta_Grind_simpEq___redArg___closed__15;
x_316 = l_Lean_Meta_Grind_pushNot___redArg___closed__60;
x_317 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set_uint8(x_317, sizeof(void*)*2, x_109);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_101, 0, x_318);
return x_101;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec_ref(x_105);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_319 = l_Lean_Meta_Grind_simpEq___redArg___closed__12;
x_320 = l_Lean_Meta_Grind_pushNot___redArg___closed__64;
x_321 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*2, x_107);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_101, 0, x_322);
return x_101;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_101, 0);
x_324 = lean_ctor_get(x_101, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_101);
x_325 = l_Lean_Expr_cleanupAnnotations(x_323);
x_326 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_327 = l_Lean_Expr_isConstOf(x_325, x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_329 = l_Lean_Expr_isConstOf(x_325, x_328);
if (x_329 == 0)
{
uint8_t x_330; 
x_330 = l_Lean_Expr_isApp(x_325);
if (x_330 == 0)
{
lean_dec_ref(x_325);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = lean_ctor_get(x_325, 1);
lean_inc_ref(x_331);
x_332 = l_Lean_Expr_appFnCleanup___redArg(x_325);
x_333 = l_Lean_Expr_isConstOf(x_332, x_18);
if (x_333 == 0)
{
uint8_t x_334; 
x_334 = l_Lean_Expr_isApp(x_332);
if (x_334 == 0)
{
lean_dec_ref(x_332);
lean_dec_ref(x_331);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_335 = lean_ctor_get(x_332, 1);
lean_inc_ref(x_335);
x_336 = l_Lean_Expr_appFnCleanup___redArg(x_332);
x_337 = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
x_338 = l_Lean_Expr_isConstOf(x_336, x_337);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_340 = l_Lean_Expr_isConstOf(x_336, x_339);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
x_342 = l_Lean_Expr_isConstOf(x_336, x_341);
if (x_342 == 0)
{
uint8_t x_343; 
x_343 = l_Lean_Expr_isApp(x_336);
if (x_343 == 0)
{
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_344 = lean_ctor_get(x_336, 1);
lean_inc_ref(x_344);
x_345 = l_Lean_Expr_appFnCleanup___redArg(x_336);
x_346 = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
x_347 = l_Lean_Expr_isConstOf(x_345, x_346);
if (x_347 == 0)
{
uint8_t x_348; 
x_348 = l_Lean_Expr_isApp(x_345);
if (x_348 == 0)
{
lean_dec_ref(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_349 = lean_ctor_get(x_345, 1);
lean_inc_ref(x_349);
x_350 = l_Lean_Expr_appFnCleanup___redArg(x_345);
x_351 = l_Lean_Meta_Grind_pushNot___redArg___closed__15;
x_352 = l_Lean_Expr_isConstOf(x_350, x_351);
if (x_352 == 0)
{
uint8_t x_353; 
x_353 = l_Lean_Expr_isApp(x_350);
if (x_353 == 0)
{
lean_dec_ref(x_350);
lean_dec_ref(x_349);
lean_dec_ref(x_344);
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = lean_ctor_get(x_350, 1);
lean_inc_ref(x_354);
x_355 = l_Lean_Expr_appFnCleanup___redArg(x_350);
x_356 = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
x_357 = l_Lean_Expr_isConstOf(x_355, x_356);
if (x_357 == 0)
{
lean_dec_ref(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_349);
lean_dec_ref(x_344);
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_324;
goto block_100;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc_ref(x_335);
x_358 = l_Lean_mkNot(x_335);
lean_inc_ref(x_331);
x_359 = l_Lean_mkNot(x_331);
lean_inc_ref(x_344);
lean_inc_ref(x_349);
x_360 = l_Lean_mkApp5(x_355, x_354, x_349, x_344, x_358, x_359);
x_361 = l_Lean_Meta_Grind_pushNot___redArg___closed__18;
x_362 = l_Lean_mkApp4(x_361, x_349, x_344, x_335, x_331);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*2, x_357);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_324);
return x_366;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
lean_dec_ref(x_350);
lean_dec_ref(x_344);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_367 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_349, x_3, x_324);
lean_dec(x_3);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
x_371 = l_Lean_Expr_cleanupAnnotations(x_368);
x_372 = l_Lean_Meta_Grind_pushNot___redArg___closed__20;
x_373 = l_Lean_Expr_isConstOf(x_371, x_372);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; 
x_374 = l_Lean_Meta_Grind_pushNot___redArg___closed__22;
x_375 = l_Lean_Expr_isConstOf(x_371, x_374);
lean_dec_ref(x_371);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_376 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_370)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_370;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_369);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_378 = l_Lean_Meta_Grind_pushNot___redArg___closed__24;
lean_inc_ref(x_331);
x_379 = l_Lean_mkIntAdd(x_331, x_378);
lean_inc_ref(x_335);
x_380 = l_Lean_mkIntLE(x_379, x_335);
x_381 = l_Lean_Meta_Grind_pushNot___redArg___closed__27;
x_382 = l_Lean_mkAppB(x_381, x_335, x_331);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
x_384 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_383);
lean_ctor_set_uint8(x_384, sizeof(void*)*2, x_375);
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_384);
if (lean_is_scalar(x_370)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_370;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_369);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec_ref(x_371);
x_387 = l_Lean_Meta_Grind_pushNot___redArg___closed__28;
lean_inc_ref(x_331);
x_388 = l_Lean_mkNatAdd(x_331, x_387);
lean_inc_ref(x_335);
x_389 = l_Lean_mkNatLE(x_388, x_335);
x_390 = l_Lean_Meta_Grind_pushNot___redArg___closed__30;
x_391 = l_Lean_mkAppB(x_390, x_335, x_331);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
x_393 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_393, 0, x_389);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*2, x_373);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
if (lean_is_scalar(x_370)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_370;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_369);
return x_395;
}
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_396 = l_Lean_Expr_isProp(x_344);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_397 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_331, x_3, x_324);
lean_dec(x_3);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
x_401 = l_Lean_Expr_cleanupAnnotations(x_398);
x_402 = l_Lean_Meta_Grind_simpEq___redArg___closed__28;
x_403 = l_Lean_Expr_isConstOf(x_401, x_402);
if (x_403 == 0)
{
lean_object* x_404; uint8_t x_405; 
x_404 = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
x_405 = l_Lean_Expr_isConstOf(x_401, x_404);
lean_dec_ref(x_401);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec_ref(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_335);
x_406 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_400)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_400;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_399);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_408 = l_Lean_Meta_Grind_pushNot___redArg___closed__31;
lean_inc_ref(x_335);
x_409 = l_Lean_mkApp3(x_345, x_344, x_335, x_408);
x_410 = l_Lean_Meta_Grind_pushNot___redArg___closed__34;
x_411 = l_Lean_Expr_app___override(x_410, x_335);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_413 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_413, 0, x_409);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set_uint8(x_413, sizeof(void*)*2, x_347);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_413);
if (lean_is_scalar(x_400)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_400;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_399);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec_ref(x_401);
x_416 = l_Lean_Meta_Grind_simpEq___redArg___closed__6;
lean_inc_ref(x_335);
x_417 = l_Lean_mkApp3(x_345, x_344, x_335, x_416);
x_418 = l_Lean_Meta_Grind_pushNot___redArg___closed__37;
x_419 = l_Lean_Expr_app___override(x_418, x_335);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
x_421 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_421, 0, x_417);
lean_ctor_set(x_421, 1, x_420);
lean_ctor_set_uint8(x_421, sizeof(void*)*2, x_347);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_421);
if (lean_is_scalar(x_400)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_400;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_399);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_3);
lean_inc_ref(x_331);
x_424 = l_Lean_mkNot(x_331);
lean_inc_ref(x_335);
x_425 = l_Lean_mkApp3(x_345, x_344, x_335, x_424);
x_426 = l_Lean_Meta_Grind_pushNot___redArg___closed__40;
x_427 = l_Lean_mkAppB(x_426, x_335, x_331);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_429 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_429, 0, x_425);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set_uint8(x_429, sizeof(void*)*2, x_347);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_324);
return x_431;
}
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec_ref(x_336);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_432 = l_Lean_Meta_Grind_pushNot___redArg___closed__41;
lean_inc_ref(x_335);
x_433 = l_Lean_mkNot(x_335);
lean_inc_ref(x_331);
x_434 = l_Lean_mkNot(x_331);
x_435 = l_Lean_mkAppB(x_432, x_433, x_434);
x_436 = l_Lean_Meta_Grind_pushNot___redArg___closed__44;
x_437 = l_Lean_mkAppB(x_436, x_335, x_331);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
x_439 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_438);
lean_ctor_set_uint8(x_439, sizeof(void*)*2, x_342);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_324);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec_ref(x_336);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_442 = l_Lean_Meta_Grind_pushNot___redArg___closed__45;
lean_inc_ref(x_335);
x_443 = l_Lean_mkNot(x_335);
lean_inc_ref(x_331);
x_444 = l_Lean_mkNot(x_331);
x_445 = l_Lean_mkAppB(x_442, x_443, x_444);
x_446 = l_Lean_Meta_Grind_pushNot___redArg___closed__48;
x_447 = l_Lean_mkAppB(x_446, x_335, x_331);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
x_449 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_448);
lean_ctor_set_uint8(x_449, sizeof(void*)*2, x_340);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_449);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_324);
return x_451;
}
}
else
{
lean_object* x_452; 
lean_dec_ref(x_336);
lean_dec_ref(x_1);
lean_inc_ref(x_335);
x_452 = l_Lean_Meta_getLevel(x_335, x_2, x_3, x_4, x_5, x_324);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_455 = x_452;
} else {
 lean_dec_ref(x_452);
 x_455 = lean_box(0);
}
x_456 = l_Lean_Meta_Grind_pushNot___redArg___closed__50;
x_457 = 0;
x_458 = l_Lean_Meta_Grind_pushNot___redArg___closed__51;
lean_inc_ref(x_331);
x_459 = l_Lean_Expr_app___override(x_331, x_458);
x_460 = l_Lean_mkNot(x_459);
lean_inc_ref(x_335);
x_461 = l_Lean_Expr_forallE___override(x_456, x_335, x_460, x_457);
x_462 = l_Lean_Meta_Grind_pushNot___redArg___closed__53;
x_463 = lean_box(0);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_453);
lean_ctor_set(x_464, 1, x_463);
x_465 = l_Lean_Expr_const___override(x_462, x_464);
x_466 = l_Lean_mkAppB(x_465, x_335, x_331);
x_467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_467, 0, x_466);
x_468 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_468, 0, x_461);
lean_ctor_set(x_468, 1, x_467);
lean_ctor_set_uint8(x_468, sizeof(void*)*2, x_338);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
if (lean_is_scalar(x_455)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_455;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_454);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_335);
lean_dec_ref(x_331);
x_471 = lean_ctor_get(x_452, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_452, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_473 = x_452;
} else {
 lean_dec_ref(x_452);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec_ref(x_332);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_475 = l_Lean_Meta_Grind_pushNot___redArg___closed__56;
lean_inc_ref(x_331);
x_476 = l_Lean_Expr_app___override(x_475, x_331);
x_477 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_477, 0, x_476);
x_478 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_478, 0, x_331);
lean_ctor_set(x_478, 1, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*2, x_333);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_478);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_324);
return x_480;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec_ref(x_325);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_481 = l_Lean_Meta_Grind_simpEq___redArg___closed__15;
x_482 = l_Lean_Meta_Grind_pushNot___redArg___closed__60;
x_483 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set_uint8(x_483, sizeof(void*)*2, x_329);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_324);
return x_485;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec_ref(x_325);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_486 = l_Lean_Meta_Grind_simpEq___redArg___closed__12;
x_487 = l_Lean_Meta_Grind_pushNot___redArg___closed__64;
x_488 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
lean_ctor_set_uint8(x_488, sizeof(void*)*2, x_327);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_324);
return x_490;
}
}
}
block_67:
{
lean_object* x_29; 
lean_inc_ref(x_25);
x_29 = l_Lean_Meta_getLevel(x_25, x_20, x_27, x_22, x_26, x_24);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_21);
lean_inc_ref(x_25);
lean_inc(x_23);
x_32 = l_Lean_Expr_lam___override(x_23, x_25, x_21, x_28);
x_33 = l_Lean_mkNot(x_21);
lean_inc_ref(x_25);
x_34 = l_Lean_Expr_lam___override(x_23, x_25, x_33, x_28);
x_35 = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_inc_ref(x_37);
x_38 = l_Lean_Expr_const___override(x_35, x_37);
lean_inc_ref(x_25);
x_39 = l_Lean_mkAppB(x_38, x_25, x_34);
x_40 = l_Lean_Meta_Grind_pushNot___redArg___closed__5;
x_41 = l_Lean_Expr_const___override(x_40, x_37);
x_42 = l_Lean_mkAppB(x_41, x_25, x_32);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_19);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
lean_inc_ref(x_21);
lean_inc_ref(x_25);
lean_inc(x_23);
x_48 = l_Lean_Expr_lam___override(x_23, x_25, x_21, x_28);
x_49 = l_Lean_mkNot(x_21);
lean_inc_ref(x_25);
x_50 = l_Lean_Expr_lam___override(x_23, x_25, x_49, x_28);
x_51 = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
lean_inc_ref(x_53);
x_54 = l_Lean_Expr_const___override(x_51, x_53);
lean_inc_ref(x_25);
x_55 = l_Lean_mkAppB(x_54, x_25, x_50);
x_56 = l_Lean_Meta_Grind_pushNot___redArg___closed__5;
x_57 = l_Lean_Expr_const___override(x_56, x_53);
x_58 = l_Lean_mkAppB(x_57, x_25, x_48);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_19);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_25);
lean_dec(x_23);
lean_dec_ref(x_21);
x_63 = !lean_is_exclusive(x_29);
if (x_63 == 0)
{
return x_29;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_86:
{
if (x_77 == 0)
{
x_20 = x_68;
x_21 = x_69;
x_22 = x_70;
x_23 = x_72;
x_24 = x_71;
x_25 = x_73;
x_26 = x_75;
x_27 = x_74;
x_28 = x_76;
goto block_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_68);
lean_inc_ref(x_69);
x_78 = l_Lean_mkNot(x_69);
lean_inc_ref(x_73);
x_79 = l_Lean_mkAnd(x_73, x_78);
x_80 = l_Lean_Meta_Grind_pushNot___redArg___closed__8;
x_81 = l_Lean_mkAppB(x_80, x_73, x_69);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_19);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_71);
return x_85;
}
}
block_100:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_94);
x_95 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_96 = l_Lean_Expr_isProp(x_93);
if (x_96 == 0)
{
x_68 = x_87;
x_69 = x_94;
x_70 = x_89;
x_71 = x_91;
x_72 = x_92;
x_73 = x_93;
x_74 = x_88;
x_75 = x_90;
x_76 = x_95;
x_77 = x_96;
goto block_86;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_Expr_hasLooseBVars(x_94);
if (x_97 == 0)
{
x_68 = x_87;
x_69 = x_94;
x_70 = x_89;
x_71 = x_91;
x_72 = x_92;
x_73 = x_93;
x_74 = x_88;
x_75 = x_90;
x_76 = x_95;
x_77 = x_96;
goto block_86;
}
else
{
x_20 = x_87;
x_21 = x_94;
x_22 = x_89;
x_23 = x_92;
x_24 = x_91;
x_25 = x_93;
x_26 = x_90;
x_27 = x_88;
x_28 = x_95;
goto block_67;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_1);
x_98 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
return x_99;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_pushNot___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_pushNot(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pushNot", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_pushNot___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_swap13", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_swap12", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__3;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_true", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_false", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_assoc", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__12;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true_or", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false_or", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpOr___redArg___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpOr___redArg___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_120 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_121 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_122 = l_Lean_Expr_isConstOf(x_120, x_121);
lean_dec_ref(x_120);
if (x_122 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_17);
goto block_14;
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_11);
lean_inc_ref(x_20);
x_123 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_20, x_2, x_10);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = l_Lean_Expr_cleanupAnnotations(x_125);
x_128 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_129 = l_Lean_Expr_isConstOf(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_131 = l_Lean_Expr_isConstOf(x_127, x_130);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Expr_isApp(x_127);
if (x_132 == 0)
{
lean_dec_ref(x_127);
lean_free_object(x_123);
x_21 = x_2;
x_22 = x_126;
goto block_119;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_133);
x_134 = l_Lean_Expr_appFnCleanup___redArg(x_127);
x_135 = l_Lean_Expr_isApp(x_134);
if (x_135 == 0)
{
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_free_object(x_123);
x_21 = x_2;
x_22 = x_126;
goto block_119;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc_ref(x_136);
x_137 = l_Lean_Expr_appFnCleanup___redArg(x_134);
x_138 = l_Lean_Expr_isConstOf(x_137, x_121);
lean_dec_ref(x_137);
if (x_138 == 0)
{
lean_dec_ref(x_136);
lean_dec_ref(x_133);
lean_free_object(x_123);
x_21 = x_2;
x_22 = x_126;
goto block_119;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_20);
lean_inc_ref(x_17);
lean_inc_ref(x_133);
x_139 = l_Lean_mkOr(x_133, x_17);
lean_inc_ref(x_136);
x_140 = l_Lean_mkOr(x_136, x_139);
x_141 = l_Lean_Meta_Grind_simpOr___redArg___closed__14;
x_142 = l_Lean_mkApp3(x_141, x_136, x_133, x_17);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_138);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_123, 0, x_145);
return x_123;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_127);
x_146 = l_Lean_Meta_Grind_simpOr___redArg___closed__17;
x_147 = l_Lean_Expr_app___override(x_146, x_17);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_149, 0, x_20);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_131);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_123, 0, x_150);
return x_123;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_127);
lean_dec_ref(x_20);
x_151 = l_Lean_Meta_Grind_simpOr___redArg___closed__20;
lean_inc_ref(x_17);
x_152 = l_Lean_Expr_app___override(x_151, x_17);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_154, 0, x_17);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_129);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_123, 0, x_155);
return x_123;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = lean_ctor_get(x_123, 0);
x_157 = lean_ctor_get(x_123, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_123);
x_158 = l_Lean_Expr_cleanupAnnotations(x_156);
x_159 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_160 = l_Lean_Expr_isConstOf(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_162 = l_Lean_Expr_isConstOf(x_158, x_161);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Expr_isApp(x_158);
if (x_163 == 0)
{
lean_dec_ref(x_158);
x_21 = x_2;
x_22 = x_157;
goto block_119;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_158, 1);
lean_inc_ref(x_164);
x_165 = l_Lean_Expr_appFnCleanup___redArg(x_158);
x_166 = l_Lean_Expr_isApp(x_165);
if (x_166 == 0)
{
lean_dec_ref(x_165);
lean_dec_ref(x_164);
x_21 = x_2;
x_22 = x_157;
goto block_119;
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc_ref(x_167);
x_168 = l_Lean_Expr_appFnCleanup___redArg(x_165);
x_169 = l_Lean_Expr_isConstOf(x_168, x_121);
lean_dec_ref(x_168);
if (x_169 == 0)
{
lean_dec_ref(x_167);
lean_dec_ref(x_164);
x_21 = x_2;
x_22 = x_157;
goto block_119;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec_ref(x_20);
lean_inc_ref(x_17);
lean_inc_ref(x_164);
x_170 = l_Lean_mkOr(x_164, x_17);
lean_inc_ref(x_167);
x_171 = l_Lean_mkOr(x_167, x_170);
x_172 = l_Lean_Meta_Grind_simpOr___redArg___closed__14;
x_173 = l_Lean_mkApp3(x_172, x_167, x_164, x_17);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*2, x_169);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_157);
return x_177;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec_ref(x_158);
x_178 = l_Lean_Meta_Grind_simpOr___redArg___closed__17;
x_179 = l_Lean_Expr_app___override(x_178, x_17);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_181, 0, x_20);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_162);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_157);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec_ref(x_158);
lean_dec_ref(x_20);
x_184 = l_Lean_Meta_Grind_simpOr___redArg___closed__20;
lean_inc_ref(x_17);
x_185 = l_Lean_Expr_app___override(x_184, x_17);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_187 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_187, 0, x_17);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_160);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_157);
return x_189;
}
}
}
block_119:
{
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_17);
x_23 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_17, x_21, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Expr_cleanupAnnotations(x_25);
x_28 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_31 = l_Lean_Expr_isConstOf(x_27, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec_ref(x_17);
x_32 = l_Lean_Expr_isApp(x_27);
if (x_32 == 0)
{
lean_dec_ref(x_27);
lean_free_object(x_23);
lean_dec_ref(x_20);
x_4 = x_26;
goto block_7;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_free_object(x_23);
lean_dec_ref(x_20);
x_4 = x_26;
goto block_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_free_object(x_23);
lean_dec_ref(x_20);
x_4 = x_26;
goto block_7;
}
else
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isForall(x_20);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isForall(x_36);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_isForall(x_33);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_20);
x_43 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_23, 0, x_43);
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc_ref(x_20);
lean_inc_ref(x_36);
x_44 = l_Lean_mkOr(x_36, x_20);
lean_inc_ref(x_33);
x_45 = l_Lean_mkOr(x_33, x_44);
x_46 = l_Lean_Meta_Grind_simpOr___redArg___closed__2;
x_47 = l_Lean_mkApp3(x_46, x_20, x_36, x_33);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_39);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_23, 0, x_50);
return x_23;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc_ref(x_33);
lean_inc_ref(x_20);
x_51 = l_Lean_mkOr(x_20, x_33);
lean_inc_ref(x_36);
x_52 = l_Lean_mkOr(x_36, x_51);
x_53 = l_Lean_Meta_Grind_simpOr___redArg___closed__5;
x_54 = l_Lean_mkApp3(x_53, x_20, x_36, x_33);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_39);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_20);
x_58 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_23, 0, x_58);
return x_23;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_27);
x_59 = l_Lean_Meta_Grind_simpOr___redArg___closed__8;
x_60 = l_Lean_Expr_app___override(x_59, x_20);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_31);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_23, 0, x_63);
return x_23;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_27);
lean_dec_ref(x_17);
x_64 = l_Lean_Meta_Grind_simpOr___redArg___closed__11;
lean_inc_ref(x_20);
x_65 = l_Lean_Expr_app___override(x_64, x_20);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_29);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_23, 0, x_68);
return x_23;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_23, 0);
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_23);
x_71 = l_Lean_Expr_cleanupAnnotations(x_69);
x_72 = l_Lean_Meta_Grind_simpEq___redArg___closed__14;
x_73 = l_Lean_Expr_isConstOf(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_Meta_Grind_simpEq___redArg___closed__11;
x_75 = l_Lean_Expr_isConstOf(x_71, x_74);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec_ref(x_17);
x_76 = l_Lean_Expr_isApp(x_71);
if (x_76 == 0)
{
lean_dec_ref(x_71);
lean_dec_ref(x_20);
x_4 = x_70;
goto block_7;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_77);
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_79 = l_Lean_Expr_isApp(x_78);
if (x_79 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_20);
x_4 = x_70;
goto block_7;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_80);
x_81 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_82 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_83 = l_Lean_Expr_isConstOf(x_81, x_82);
lean_dec_ref(x_81);
if (x_83 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec_ref(x_20);
x_4 = x_70;
goto block_7;
}
else
{
uint8_t x_84; 
x_84 = l_Lean_Expr_isForall(x_20);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = l_Lean_Expr_isForall(x_80);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Expr_isForall(x_77);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec_ref(x_20);
x_87 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_70);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc_ref(x_20);
lean_inc_ref(x_80);
x_89 = l_Lean_mkOr(x_80, x_20);
lean_inc_ref(x_77);
x_90 = l_Lean_mkOr(x_77, x_89);
x_91 = l_Lean_Meta_Grind_simpOr___redArg___closed__2;
x_92 = l_Lean_mkApp3(x_91, x_20, x_80, x_77);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_83);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_70);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_inc_ref(x_77);
lean_inc_ref(x_20);
x_97 = l_Lean_mkOr(x_20, x_77);
lean_inc_ref(x_80);
x_98 = l_Lean_mkOr(x_80, x_97);
x_99 = l_Lean_Meta_Grind_simpOr___redArg___closed__5;
x_100 = l_Lean_mkApp3(x_99, x_20, x_80, x_77);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_83);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_70);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec_ref(x_20);
x_105 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_70);
return x_106;
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_71);
x_107 = l_Lean_Meta_Grind_simpOr___redArg___closed__8;
x_108 = l_Lean_Expr_app___override(x_107, x_20);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_110, 0, x_17);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_75);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_70);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_71);
lean_dec_ref(x_17);
x_113 = l_Lean_Meta_Grind_simpOr___redArg___closed__11;
lean_inc_ref(x_20);
x_114 = l_Lean_Expr_app___override(x_113, x_20);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_116, 0, x_20);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_73);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_70);
return x_118;
}
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpOr___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_simpOr___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpOr", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpOr___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_12 = l_Lean_Meta_Grind_simpEq___redArg___closed__15;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_mkNoConfusion(x_12, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0;
x_24 = lean_array_push(x_23, x_3);
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_24, x_21, x_1, x_2, x_1, x_2, x_25, x_7, x_8, x_9, x_10, x_22);
lean_dec_ref(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_Meta_Context_config(x_7);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint64_t x_41; uint8_t x_42; 
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_7, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 6);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 1);
x_39 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 2);
x_40 = 1;
lean_ctor_set_uint8(x_29, 9, x_40);
x_41 = l_Lean_Meta_Context_configKey(x_7);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_7, 6);
lean_dec(x_43);
x_44 = lean_ctor_get(x_7, 5);
lean_dec(x_44);
x_45 = lean_ctor_get(x_7, 4);
lean_dec(x_45);
x_46 = lean_ctor_get(x_7, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_7, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_7, 0);
lean_dec(x_49);
x_50 = 2;
x_51 = lean_uint64_shift_right(x_41, x_50);
x_52 = lean_uint64_shift_left(x_51, x_50);
x_53 = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1;
x_54 = lean_uint64_lor(x_52, x_53);
x_55 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_55, 0, x_29);
lean_ctor_set_uint64(x_55, sizeof(void*)*1, x_54);
lean_ctor_set(x_7, 0, x_55);
x_56 = l_Lean_Meta_mkEqFalse_x27(x_27, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_13 = x_57;
x_14 = x_58;
goto block_19;
}
else
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec_ref(x_56);
x_13 = x_59;
x_14 = x_60;
goto block_19;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_7);
x_65 = 2;
x_66 = lean_uint64_shift_right(x_41, x_65);
x_67 = lean_uint64_shift_left(x_66, x_65);
x_68 = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1;
x_69 = lean_uint64_lor(x_67, x_68);
x_70 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_70, 0, x_29);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_69);
x_71 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_32);
lean_ctor_set(x_71, 2, x_33);
lean_ctor_set(x_71, 3, x_34);
lean_ctor_set(x_71, 4, x_35);
lean_ctor_set(x_71, 5, x_36);
lean_ctor_set(x_71, 6, x_37);
lean_ctor_set_uint8(x_71, sizeof(void*)*7, x_31);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 1, x_38);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 2, x_39);
x_72 = l_Lean_Meta_mkEqFalse_x27(x_27, x_71, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_13 = x_73;
x_14 = x_74;
goto block_19;
}
else
{
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_13 = x_75;
x_14 = x_76;
goto block_19;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
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
else
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_81 = lean_ctor_get_uint8(x_29, 0);
x_82 = lean_ctor_get_uint8(x_29, 1);
x_83 = lean_ctor_get_uint8(x_29, 2);
x_84 = lean_ctor_get_uint8(x_29, 3);
x_85 = lean_ctor_get_uint8(x_29, 4);
x_86 = lean_ctor_get_uint8(x_29, 5);
x_87 = lean_ctor_get_uint8(x_29, 6);
x_88 = lean_ctor_get_uint8(x_29, 7);
x_89 = lean_ctor_get_uint8(x_29, 8);
x_90 = lean_ctor_get_uint8(x_29, 10);
x_91 = lean_ctor_get_uint8(x_29, 11);
x_92 = lean_ctor_get_uint8(x_29, 12);
x_93 = lean_ctor_get_uint8(x_29, 13);
x_94 = lean_ctor_get_uint8(x_29, 14);
x_95 = lean_ctor_get_uint8(x_29, 15);
x_96 = lean_ctor_get_uint8(x_29, 16);
x_97 = lean_ctor_get_uint8(x_29, 17);
x_98 = lean_ctor_get_uint8(x_29, 18);
lean_dec(x_29);
x_99 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
x_100 = lean_ctor_get(x_7, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_7, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_7, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_7, 6);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 1);
x_107 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 2);
x_108 = 1;
x_109 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_109, 0, x_81);
lean_ctor_set_uint8(x_109, 1, x_82);
lean_ctor_set_uint8(x_109, 2, x_83);
lean_ctor_set_uint8(x_109, 3, x_84);
lean_ctor_set_uint8(x_109, 4, x_85);
lean_ctor_set_uint8(x_109, 5, x_86);
lean_ctor_set_uint8(x_109, 6, x_87);
lean_ctor_set_uint8(x_109, 7, x_88);
lean_ctor_set_uint8(x_109, 8, x_89);
lean_ctor_set_uint8(x_109, 9, x_108);
lean_ctor_set_uint8(x_109, 10, x_90);
lean_ctor_set_uint8(x_109, 11, x_91);
lean_ctor_set_uint8(x_109, 12, x_92);
lean_ctor_set_uint8(x_109, 13, x_93);
lean_ctor_set_uint8(x_109, 14, x_94);
lean_ctor_set_uint8(x_109, 15, x_95);
lean_ctor_set_uint8(x_109, 16, x_96);
lean_ctor_set_uint8(x_109, 17, x_97);
lean_ctor_set_uint8(x_109, 18, x_98);
x_110 = l_Lean_Meta_Context_configKey(x_7);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 x_111 = x_7;
} else {
 lean_dec_ref(x_7);
 x_111 = lean_box(0);
}
x_112 = 2;
x_113 = lean_uint64_shift_right(x_110, x_112);
x_114 = lean_uint64_shift_left(x_113, x_112);
x_115 = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1;
x_116 = lean_uint64_lor(x_114, x_115);
x_117 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set_uint64(x_117, sizeof(void*)*1, x_116);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 7, 3);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_100);
lean_ctor_set(x_118, 2, x_101);
lean_ctor_set(x_118, 3, x_102);
lean_ctor_set(x_118, 4, x_103);
lean_ctor_set(x_118, 5, x_104);
lean_ctor_set(x_118, 6, x_105);
lean_ctor_set_uint8(x_118, sizeof(void*)*7, x_99);
lean_ctor_set_uint8(x_118, sizeof(void*)*7 + 1, x_106);
lean_ctor_set_uint8(x_118, sizeof(void*)*7 + 2, x_107);
x_119 = l_Lean_Meta_mkEqFalse_x27(x_27, x_118, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_13 = x_120;
x_14 = x_121;
goto block_19;
}
else
{
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec_ref(x_119);
x_13 = x_122;
x_14 = x_123;
goto block_19;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
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
}
}
else
{
uint8_t x_128; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_128 = !lean_is_exclusive(x_26);
if (x_128 == 0)
{
return x_26;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_26, 0);
x_130 = lean_ctor_get(x_26, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_26);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_132 = !lean_is_exclusive(x_20);
if (x_132 == 0)
{
return x_20;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_20, 0);
x_134 = lean_ctor_get(x_20, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_20);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_17 = l_Lean_Expr_cleanupAnnotations(x_11);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
lean_dec_ref(x_25);
if (x_27 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_16;
}
else
{
lean_object* x_28; 
lean_dec(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_28 = l_Lean_Meta_isConstructorApp_x3f(x_22, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_28, 1);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec_ref(x_29);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = l_Lean_Meta_isConstructorApp_x3f(x_19, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
lean_ctor_set(x_28, 1, x_42);
lean_ctor_set(x_28, 0, x_47);
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_28);
x_48 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec_ref(x_41);
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec_ref(x_48);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_name_eq(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
if (x_27 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_43);
x_54 = lean_box(x_53);
x_55 = lean_box(x_27);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed), 11, 2);
lean_closure_set(x_56, 0, x_54);
lean_closure_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
x_58 = l_Lean_Meta_withLocalDeclD___at___reduceCtorEq_spec__0___redArg(x_57, x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
return x_58;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_46;
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_59; 
lean_dec(x_39);
lean_free_object(x_28);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_ctor_get(x_29, 0);
lean_inc(x_64);
lean_dec_ref(x_29);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_65 = l_Lean_Meta_isConstructorApp_x3f(x_19, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_72 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_74);
lean_dec(x_64);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
lean_dec_ref(x_66);
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec_ref(x_74);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_name_eq(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
if (x_27 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_68);
x_80 = lean_box(x_79);
x_81 = lean_box(x_27);
x_82 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed), 11, 2);
lean_closure_set(x_82, 0, x_80);
lean_closure_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
x_84 = l_Lean_Meta_withLocalDeclD___at___reduceCtorEq_spec__0___redArg(x_83, x_1, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
return x_84;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_71;
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_65, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_65, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_87 = x_65;
} else {
 lean_dec_ref(x_65);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_28);
if (x_89 == 0)
{
return x_28;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_28, 0);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_28);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
if (lean_is_scalar(x_13)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_13;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceCtorEqCheap", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_;
x_2 = l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_3 = l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_4 = l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_;
x_3 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceReplicate", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceCtorEq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
x_8 = l_Lean_Meta_Simp_Simprocs_erase(x_5, x_7);
x_9 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__4;
x_10 = l_Lean_Meta_Simp_Simprocs_erase(x_8, x_9);
x_11 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_;
x_12 = 1;
x_13 = l_Lean_Meta_Simp_Simprocs_add(x_10, x_11, x_12, x_1, x_2, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(x_14, x_1, x_2, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Meta_Grind_addPreMatchCondSimproc(x_17, x_1, x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Meta_Grind_Arith_addSimproc(x_20, x_1, x_2, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Meta_Grind_addForallSimproc(x_23, x_1, x_2, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_;
x_29 = l_Lean_Meta_Simp_Simprocs_add(x_26, x_28, x_12, x_1, x_2, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_;
x_33 = l_Lean_Meta_Simp_Simprocs_add(x_30, x_32, x_12, x_1, x_2, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_;
x_37 = l_Lean_Meta_Simp_Simprocs_add(x_34, x_36, x_12, x_1, x_2, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_;
x_41 = 0;
x_42 = l_Lean_Meta_Simp_Simprocs_add(x_38, x_40, x_41, x_1, x_2, x_39);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__5;
x_46 = lean_array_push(x_45, x_44);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = l_Lean_Meta_Grind_getSimprocs___redArg___closed__5;
x_50 = lean_array_push(x_49, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_33);
if (x_60 == 0)
{
return x_33;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
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
x_64 = !lean_is_exclusive(x_29);
if (x_64 == 0)
{
return x_29;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_29, 0);
x_66 = lean_ctor_get(x_29, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_29);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
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
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_22, 0);
x_74 = lean_ctor_get(x_22, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_22);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_19);
if (x_76 == 0)
{
return x_19;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_19, 0);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_19);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_16);
if (x_80 == 0)
{
return x_16;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_16, 0);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_16);
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
x_84 = !lean_is_exclusive(x_13);
if (x_84 == 0)
{
return x_13;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_13, 0);
x_86 = lean_ctor_get(x_13, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_13);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getSimprocs___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getSimprocs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = 1;
lean_inc(x_2);
x_14 = l_Lean_Environment_contains(x_12, x_2, x_13);
if (x_14 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_2);
x_20 = l_Lean_Environment_contains(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_1, x_2, x_3, x_4, x_5, x_6, x_17);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimpContext___closed__1;
x_2 = l_Lean_Meta_Grind_getSimpContext___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimpContext___closed__4;
x_2 = l_Lean_Meta_Grind_getSimpContext___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimpContext___closed__6;
x_2 = l_Lean_Meta_Grind_pushNot___redArg___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("xor", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_getSimpContext___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_getSimpContext___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getSimpContext___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
x_8 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_Grind_getSimpContext___closed__2;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_Grind_getSimpContext___closed__5;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(x_13, x_15, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Meta_Grind_getSimpContext___closed__7;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(x_17, x_19, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Meta_Grind_getSimpContext___closed__9;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(x_21, x_23, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_Meta_Grind_getSimpContext___closed__11;
lean_inc(x_5);
lean_inc_ref(x_2);
x_28 = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(x_25, x_27, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_5, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 15);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 16);
x_36 = lean_unsigned_to_nat(100000u);
x_37 = lean_unsigned_to_nat(2u);
x_38 = 0;
x_39 = 1;
x_40 = 0;
x_41 = lean_alloc_ctor(0, 2, 24);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 1, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 2, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 3, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 4, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 5, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 6, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 7, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 9, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 10, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 11, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 12, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 13, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 14, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 15, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 17, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 18, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 19, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 20, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 21, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 22, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 23, x_39);
x_42 = l_Lean_Meta_Grind_getSimpContext___closed__12;
x_43 = lean_array_push(x_42, x_29);
x_44 = l_Lean_Meta_Simp_mkContext___redArg(x_41, x_43, x_32, x_2, x_5, x_33);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_normalizeImp___closed__4;
x_4 = l_Lean_Meta_Grind_normalizeImp___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__6;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__3;
x_3 = l_Lean_Meta_Grind_normalizeImp___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_normalizeImp___closed__7;
x_2 = l_Lean_Meta_Grind_normalizeImp___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_Grind_getSimpContext(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_Grind_getSimprocs___redArg(x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_Grind_normalizeImp___closed__8;
x_16 = l_Lean_Meta_simp(x_1, x_9, x_12, x_14, x_15, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_21);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
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
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_ = _init_l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_();
lean_mark_persistent(l_Lean_Meta_Grind_initFn___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_);
if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
}l_Lean_Meta_Grind_registerNormTheorems___closed__0 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__0);
l_Lean_Meta_Grind_registerNormTheorems___closed__1 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__1);
l_Lean_Meta_Grind_registerNormTheorems___closed__2 = _init_l_Lean_Meta_Grind_registerNormTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_registerNormTheorems___closed__2);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12);
l_Lean_Meta_Grind_simpEq___redArg___closed__0 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__0);
l_Lean_Meta_Grind_simpEq___redArg___closed__1 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__1);
l_Lean_Meta_Grind_simpEq___redArg___closed__2 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__2);
l_Lean_Meta_Grind_simpEq___redArg___closed__3 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__3);
l_Lean_Meta_Grind_simpEq___redArg___closed__4 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__4);
l_Lean_Meta_Grind_simpEq___redArg___closed__5 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__5);
l_Lean_Meta_Grind_simpEq___redArg___closed__6 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__6);
l_Lean_Meta_Grind_simpEq___redArg___closed__7 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__7);
l_Lean_Meta_Grind_simpEq___redArg___closed__8 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__8);
l_Lean_Meta_Grind_simpEq___redArg___closed__9 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__9);
l_Lean_Meta_Grind_simpEq___redArg___closed__10 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__10);
l_Lean_Meta_Grind_simpEq___redArg___closed__11 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__11);
l_Lean_Meta_Grind_simpEq___redArg___closed__12 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__12);
l_Lean_Meta_Grind_simpEq___redArg___closed__13 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__13);
l_Lean_Meta_Grind_simpEq___redArg___closed__14 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__14);
l_Lean_Meta_Grind_simpEq___redArg___closed__15 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__15);
l_Lean_Meta_Grind_simpEq___redArg___closed__16 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__16);
l_Lean_Meta_Grind_simpEq___redArg___closed__17 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__17);
l_Lean_Meta_Grind_simpEq___redArg___closed__18 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__18);
l_Lean_Meta_Grind_simpEq___redArg___closed__19 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__19);
l_Lean_Meta_Grind_simpEq___redArg___closed__20 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__20);
l_Lean_Meta_Grind_simpEq___redArg___closed__21 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__21);
l_Lean_Meta_Grind_simpEq___redArg___closed__22 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__22);
l_Lean_Meta_Grind_simpEq___redArg___closed__23 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__23();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__23);
l_Lean_Meta_Grind_simpEq___redArg___closed__24 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__24();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__24);
l_Lean_Meta_Grind_simpEq___redArg___closed__25 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__25);
l_Lean_Meta_Grind_simpEq___redArg___closed__26 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__26();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__26);
l_Lean_Meta_Grind_simpEq___redArg___closed__27 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__27();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__27);
l_Lean_Meta_Grind_simpEq___redArg___closed__28 = _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28();
lean_mark_persistent(l_Lean_Meta_Grind_simpEq___redArg___closed__28);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__14____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1020_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_simpDIte___redArg___closed__0 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__0);
l_Lean_Meta_Grind_simpDIte___redArg___closed__1 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__1);
l_Lean_Meta_Grind_simpDIte___redArg___closed__2 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__2);
l_Lean_Meta_Grind_simpDIte___redArg___closed__3 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__3);
l_Lean_Meta_Grind_simpDIte___redArg___closed__4 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__4);
l_Lean_Meta_Grind_simpDIte___redArg___closed__5 = _init_l_Lean_Meta_Grind_simpDIte___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpDIte___redArg___closed__5);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__7____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__8____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19___closed__9____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__19____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_1531_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_pushNot___redArg___closed__0 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__0);
l_Lean_Meta_Grind_pushNot___redArg___closed__1 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__1);
l_Lean_Meta_Grind_pushNot___redArg___closed__2 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__2);
l_Lean_Meta_Grind_pushNot___redArg___closed__3 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__3);
l_Lean_Meta_Grind_pushNot___redArg___closed__4 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__4);
l_Lean_Meta_Grind_pushNot___redArg___closed__5 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__5);
l_Lean_Meta_Grind_pushNot___redArg___closed__6 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__6);
l_Lean_Meta_Grind_pushNot___redArg___closed__7 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__7);
l_Lean_Meta_Grind_pushNot___redArg___closed__8 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__8);
l_Lean_Meta_Grind_pushNot___redArg___closed__9 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__9);
l_Lean_Meta_Grind_pushNot___redArg___closed__10 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__10);
l_Lean_Meta_Grind_pushNot___redArg___closed__11 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__11);
l_Lean_Meta_Grind_pushNot___redArg___closed__12 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__12);
l_Lean_Meta_Grind_pushNot___redArg___closed__13 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__13);
l_Lean_Meta_Grind_pushNot___redArg___closed__14 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__14);
l_Lean_Meta_Grind_pushNot___redArg___closed__15 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__15);
l_Lean_Meta_Grind_pushNot___redArg___closed__16 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__16);
l_Lean_Meta_Grind_pushNot___redArg___closed__17 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__17);
l_Lean_Meta_Grind_pushNot___redArg___closed__18 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__18);
l_Lean_Meta_Grind_pushNot___redArg___closed__19 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__19);
l_Lean_Meta_Grind_pushNot___redArg___closed__20 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__20);
l_Lean_Meta_Grind_pushNot___redArg___closed__21 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__21);
l_Lean_Meta_Grind_pushNot___redArg___closed__22 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__22);
l_Lean_Meta_Grind_pushNot___redArg___closed__23 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__23);
l_Lean_Meta_Grind_pushNot___redArg___closed__24 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__24);
l_Lean_Meta_Grind_pushNot___redArg___closed__25 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__25);
l_Lean_Meta_Grind_pushNot___redArg___closed__26 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__26);
l_Lean_Meta_Grind_pushNot___redArg___closed__27 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__27);
l_Lean_Meta_Grind_pushNot___redArg___closed__28 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__28);
l_Lean_Meta_Grind_pushNot___redArg___closed__29 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__29);
l_Lean_Meta_Grind_pushNot___redArg___closed__30 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__30);
l_Lean_Meta_Grind_pushNot___redArg___closed__31 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__31);
l_Lean_Meta_Grind_pushNot___redArg___closed__32 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__32);
l_Lean_Meta_Grind_pushNot___redArg___closed__33 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__33();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__33);
l_Lean_Meta_Grind_pushNot___redArg___closed__34 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__34);
l_Lean_Meta_Grind_pushNot___redArg___closed__35 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__35);
l_Lean_Meta_Grind_pushNot___redArg___closed__36 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__36);
l_Lean_Meta_Grind_pushNot___redArg___closed__37 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__37);
l_Lean_Meta_Grind_pushNot___redArg___closed__38 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__38();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__38);
l_Lean_Meta_Grind_pushNot___redArg___closed__39 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__39);
l_Lean_Meta_Grind_pushNot___redArg___closed__40 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__40);
l_Lean_Meta_Grind_pushNot___redArg___closed__41 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__41);
l_Lean_Meta_Grind_pushNot___redArg___closed__42 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__42();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__42);
l_Lean_Meta_Grind_pushNot___redArg___closed__43 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__43);
l_Lean_Meta_Grind_pushNot___redArg___closed__44 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__44);
l_Lean_Meta_Grind_pushNot___redArg___closed__45 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__45);
l_Lean_Meta_Grind_pushNot___redArg___closed__46 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__46);
l_Lean_Meta_Grind_pushNot___redArg___closed__47 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__47();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__47);
l_Lean_Meta_Grind_pushNot___redArg___closed__48 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__48);
l_Lean_Meta_Grind_pushNot___redArg___closed__49 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__49();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__49);
l_Lean_Meta_Grind_pushNot___redArg___closed__50 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__50();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__50);
l_Lean_Meta_Grind_pushNot___redArg___closed__51 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__51);
l_Lean_Meta_Grind_pushNot___redArg___closed__52 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__52();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__52);
l_Lean_Meta_Grind_pushNot___redArg___closed__53 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__53();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__53);
l_Lean_Meta_Grind_pushNot___redArg___closed__54 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__54);
l_Lean_Meta_Grind_pushNot___redArg___closed__55 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__55);
l_Lean_Meta_Grind_pushNot___redArg___closed__56 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__56);
l_Lean_Meta_Grind_pushNot___redArg___closed__57 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__57();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__57);
l_Lean_Meta_Grind_pushNot___redArg___closed__58 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__58);
l_Lean_Meta_Grind_pushNot___redArg___closed__59 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__59);
l_Lean_Meta_Grind_pushNot___redArg___closed__60 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__60);
l_Lean_Meta_Grind_pushNot___redArg___closed__61 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__61();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__61);
l_Lean_Meta_Grind_pushNot___redArg___closed__62 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__62();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__62);
l_Lean_Meta_Grind_pushNot___redArg___closed__63 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__63);
l_Lean_Meta_Grind_pushNot___redArg___closed__64 = _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64();
lean_mark_persistent(l_Lean_Meta_Grind_pushNot___redArg___closed__64);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__24____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_2724_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_simpOr___redArg___closed__0 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__0);
l_Lean_Meta_Grind_simpOr___redArg___closed__1 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__1);
l_Lean_Meta_Grind_simpOr___redArg___closed__2 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__2);
l_Lean_Meta_Grind_simpOr___redArg___closed__3 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__3);
l_Lean_Meta_Grind_simpOr___redArg___closed__4 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__4);
l_Lean_Meta_Grind_simpOr___redArg___closed__5 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__5);
l_Lean_Meta_Grind_simpOr___redArg___closed__6 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__6);
l_Lean_Meta_Grind_simpOr___redArg___closed__7 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__7);
l_Lean_Meta_Grind_simpOr___redArg___closed__8 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__8);
l_Lean_Meta_Grind_simpOr___redArg___closed__9 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__9);
l_Lean_Meta_Grind_simpOr___redArg___closed__10 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__10);
l_Lean_Meta_Grind_simpOr___redArg___closed__11 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__11);
l_Lean_Meta_Grind_simpOr___redArg___closed__12 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__12);
l_Lean_Meta_Grind_simpOr___redArg___closed__13 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__13);
l_Lean_Meta_Grind_simpOr___redArg___closed__14 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__14);
l_Lean_Meta_Grind_simpOr___redArg___closed__15 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__15);
l_Lean_Meta_Grind_simpOr___redArg___closed__16 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__16);
l_Lean_Meta_Grind_simpOr___redArg___closed__17 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__17);
l_Lean_Meta_Grind_simpOr___redArg___closed__18 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__18);
l_Lean_Meta_Grind_simpOr___redArg___closed__19 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__19);
l_Lean_Meta_Grind_simpOr___redArg___closed__20 = _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_simpOr___redArg___closed__20);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__2____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__3____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__4____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__5____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29___closed__6____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__29____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3463_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0 = _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0);
l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1 = _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__1();
l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0 = _init_l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0);
l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1 = _init_l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__0____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_);
l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_ = _init_l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34___closed__1____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__34____x40_Lean_Meta_Tactic_Grind_SimpUtil___hyg_3855_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_getSimprocs___redArg___closed__0 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__1 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__2 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__3 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__4 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4);
l_Lean_Meta_Grind_getSimprocs___redArg___closed__5 = _init_l_Lean_Meta_Grind_getSimprocs___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_getSimprocs___redArg___closed__5);
l_Lean_Meta_Grind_getSimpContext___closed__0 = _init_l_Lean_Meta_Grind_getSimpContext___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__0);
l_Lean_Meta_Grind_getSimpContext___closed__1 = _init_l_Lean_Meta_Grind_getSimpContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__1);
l_Lean_Meta_Grind_getSimpContext___closed__2 = _init_l_Lean_Meta_Grind_getSimpContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__2);
l_Lean_Meta_Grind_getSimpContext___closed__3 = _init_l_Lean_Meta_Grind_getSimpContext___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__3);
l_Lean_Meta_Grind_getSimpContext___closed__4 = _init_l_Lean_Meta_Grind_getSimpContext___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__4);
l_Lean_Meta_Grind_getSimpContext___closed__5 = _init_l_Lean_Meta_Grind_getSimpContext___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__5);
l_Lean_Meta_Grind_getSimpContext___closed__6 = _init_l_Lean_Meta_Grind_getSimpContext___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__6);
l_Lean_Meta_Grind_getSimpContext___closed__7 = _init_l_Lean_Meta_Grind_getSimpContext___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__7);
l_Lean_Meta_Grind_getSimpContext___closed__8 = _init_l_Lean_Meta_Grind_getSimpContext___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__8);
l_Lean_Meta_Grind_getSimpContext___closed__9 = _init_l_Lean_Meta_Grind_getSimpContext___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__9);
l_Lean_Meta_Grind_getSimpContext___closed__10 = _init_l_Lean_Meta_Grind_getSimpContext___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__10);
l_Lean_Meta_Grind_getSimpContext___closed__11 = _init_l_Lean_Meta_Grind_getSimpContext___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__11);
l_Lean_Meta_Grind_getSimpContext___closed__12 = _init_l_Lean_Meta_Grind_getSimpContext___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_getSimpContext___closed__12);
l_Lean_Meta_Grind_normalizeImp___closed__0 = _init_l_Lean_Meta_Grind_normalizeImp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__0);
l_Lean_Meta_Grind_normalizeImp___closed__1 = _init_l_Lean_Meta_Grind_normalizeImp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__1);
l_Lean_Meta_Grind_normalizeImp___closed__2 = _init_l_Lean_Meta_Grind_normalizeImp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__2);
l_Lean_Meta_Grind_normalizeImp___closed__3 = _init_l_Lean_Meta_Grind_normalizeImp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__3);
l_Lean_Meta_Grind_normalizeImp___closed__4 = _init_l_Lean_Meta_Grind_normalizeImp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__4);
l_Lean_Meta_Grind_normalizeImp___closed__5 = _init_l_Lean_Meta_Grind_normalizeImp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__5);
l_Lean_Meta_Grind_normalizeImp___closed__6 = _init_l_Lean_Meta_Grind_normalizeImp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__6);
l_Lean_Meta_Grind_normalizeImp___closed__7 = _init_l_Lean_Meta_Grind_normalizeImp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__7);
l_Lean_Meta_Grind_normalizeImp___closed__8 = _init_l_Lean_Meta_Grind_normalizeImp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeImp___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
