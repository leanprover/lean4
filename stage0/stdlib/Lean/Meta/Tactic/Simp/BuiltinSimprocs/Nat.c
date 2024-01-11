// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: Init Lean.Meta.Offset Lean.Meta.Tactic.Simp.Simproc
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__3;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_657_(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_774_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSub___closed__2;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7;
static lean_object* l_Nat_reduceSub___closed__1;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6;
static lean_object* l_Nat_reduceDiv___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_813_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6;
static lean_object* l_Nat_reduceMod___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2;
static lean_object* l_Nat_reduceDiv___closed__2;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_562_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2;
static lean_object* l_Nat_reduceBinPred___closed__8;
static lean_object* l_Nat_reduceMul___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3;
static lean_object* l_Nat_reduceDiv___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_638_(lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655_(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7;
static lean_object* l_Nat_reduceBinPred___closed__11;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636_(lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__9;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_410_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1;
static lean_object* l_Nat_reduceBinPred___closed__17;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2;
static lean_object* l_Nat_reduceBinPred___closed__15;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGE___closed__2;
static lean_object* l_Nat_reduceGcd___closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6;
static lean_object* l_Nat_reduceLE___closed__1;
static lean_object* l_Nat_reduceSub___closed__3;
static lean_object* l_Nat_reduceBinPred___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_486_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2;
static lean_object* l_Nat_reduceBinPred___closed__14;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10;
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3;
static lean_object* l_Nat_reduceGT___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9;
static lean_object* l_Nat_reduceBinPred___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4;
static lean_object* l_Nat_reduceLT___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2;
static lean_object* l_Nat_reduceBin___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2;
static lean_object* l_Nat_reduceLT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8;
static lean_object* l_Nat_reduceBinPred___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__7;
static lean_object* l_Nat_reduceLE___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Nat_reduceMod___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_735_(lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2;
static lean_object* l_Nat_reduceBinPred___closed__6;
static lean_object* l_Nat_reduceBinPred___closed__13;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_448_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1;
static lean_object* l_Nat_reduceAdd___closed__2;
static lean_object* l_Nat_reduceGE___closed__3;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4;
static lean_object* l_Nat_reduceSucc___closed__2;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_696_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__1;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_600_(lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__12;
static lean_object* l_Nat_reduceMul___closed__1;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__19;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__20;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGcd___closed__2;
static lean_object* l_Nat_reduceBinPred___closed__2;
static lean_object* l_Nat_reduceGT___closed__2;
static lean_object* l_Nat_reduceMod___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4;
static lean_object* l_Nat_reduceBinPred___closed__18;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSucc___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694_(lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__16;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_524_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceMul___closed__3;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3;
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1;
static lean_object* l_Nat_reduceGE___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4;
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733_(lean_object*);
static lean_object* l_Nat_reduceLE___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13;
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__2;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1;
static lean_object* l_Nat_reduceLT___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__1;
static lean_object* l_Nat_reduceBinPred___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3;
static lean_object* l_Nat_reduceSucc___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10;
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalNat(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_appArg_x21(x_4);
x_17 = l_Nat_fromExpr_x3f(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
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
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_apply_1(x_3, x_28);
x_30 = l_Lean_mkNatLit(x_29);
x_31 = lean_box(0);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_18, 0, x_34);
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_apply_1(x_3, x_35);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_ctor_get(x_18, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_45 = x_18;
} else {
 lean_dec_ref(x_18);
 x_45 = lean_box(0);
}
x_46 = lean_apply_1(x_3, x_44);
x_47 = l_Lean_mkNatLit(x_46);
x_48 = lean_box(0);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
return x_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_17, 0);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_17);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Nat_reduceBin___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_14 = x_77;
x_15 = x_12;
goto block_76;
}
else
{
lean_object* x_78; 
x_78 = l_Nat_reduceBin___closed__1;
x_14 = x_78;
x_15 = x_12;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_18 = l_Lean_Expr_appFn_x21(x_4);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Nat_fromExpr_x3f(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Expr_appArg_x21(x_4);
x_31 = l_Nat_fromExpr_x3f(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_apply_2(x_3, x_29, x_42);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_32, 0, x_48);
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_apply_2(x_3, x_29, x_49);
x_51 = l_Lean_mkNatLit(x_50);
x_52 = lean_box(0);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_31, 0, x_56);
return x_31;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_dec(x_31);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_59 = x_32;
} else {
 lean_dec_ref(x_32);
 x_59 = lean_box(0);
}
x_60 = lean_apply_2(x_3, x_29, x_58);
x_61 = l_Lean_mkNatLit(x_60);
x_62 = lean_box(0);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_59;
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_29);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_31);
if (x_68 == 0)
{
return x_31;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_31, 0);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_31);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_20);
if (x_72 == 0)
{
return x_20;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_20, 0);
x_74 = lean_ctor_get(x_20, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_20);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___closed__1;
x_2 = l_Nat_reduceBinPred___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___closed__1;
x_2 = l_Nat_reduceBinPred___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_251; 
x_251 = lean_box(0);
x_14 = x_251;
x_15 = x_12;
goto block_250;
}
else
{
lean_object* x_252; 
x_252 = l_Nat_reduceBin___closed__1;
x_14 = x_252;
x_15 = x_12;
goto block_250;
}
block_250:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_18 = l_Lean_Expr_appFn_x21(x_4);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Nat_fromExpr_x3f(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_32 = l_Nat_fromExpr_x3f(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_43 = l_Lean_Meta_mkDecide(x_4, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_apply_2(x_3, x_30, x_42);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Nat_reduceBinPred___closed__4;
x_49 = l_Lean_Meta_mkEqRefl(x_48, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_Lean_Expr_appArg_x21(x_44);
lean_dec(x_44);
x_53 = l_Nat_reduceBinPred___closed__11;
x_54 = lean_array_push(x_53, x_4);
x_55 = lean_array_push(x_54, x_52);
x_56 = lean_array_push(x_55, x_51);
x_57 = l_Nat_reduceBinPred___closed__10;
x_58 = l_Lean_mkAppN(x_57, x_56);
lean_ctor_set(x_33, 0, x_58);
x_59 = l_Nat_reduceBinPred___closed__7;
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_33);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_21, 0, x_62);
lean_ctor_set(x_49, 0, x_21);
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_49, 0);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_49);
x_65 = l_Lean_Expr_appArg_x21(x_44);
lean_dec(x_44);
x_66 = l_Nat_reduceBinPred___closed__11;
x_67 = lean_array_push(x_66, x_4);
x_68 = lean_array_push(x_67, x_65);
x_69 = lean_array_push(x_68, x_63);
x_70 = l_Nat_reduceBinPred___closed__10;
x_71 = l_Lean_mkAppN(x_70, x_69);
lean_ctor_set(x_33, 0, x_71);
x_72 = l_Nat_reduceBinPred___closed__7;
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_33);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_21, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_21);
lean_ctor_set(x_76, 1, x_64);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_44);
lean_free_object(x_33);
lean_free_object(x_21);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_49);
if (x_77 == 0)
{
return x_49;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_49, 0);
x_79 = lean_ctor_get(x_49, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_49);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Nat_reduceBinPred___closed__14;
x_82 = l_Lean_Meta_mkEqRefl(x_81, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = l_Lean_Expr_appArg_x21(x_44);
lean_dec(x_44);
x_86 = l_Nat_reduceBinPred___closed__11;
x_87 = lean_array_push(x_86, x_4);
x_88 = lean_array_push(x_87, x_85);
x_89 = lean_array_push(x_88, x_84);
x_90 = l_Nat_reduceBinPred___closed__20;
x_91 = l_Lean_mkAppN(x_90, x_89);
lean_ctor_set(x_33, 0, x_91);
x_92 = l_Nat_reduceBinPred___closed__17;
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_33);
lean_ctor_set(x_94, 2, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_21, 0, x_95);
lean_ctor_set(x_82, 0, x_21);
return x_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_82);
x_98 = l_Lean_Expr_appArg_x21(x_44);
lean_dec(x_44);
x_99 = l_Nat_reduceBinPred___closed__11;
x_100 = lean_array_push(x_99, x_4);
x_101 = lean_array_push(x_100, x_98);
x_102 = lean_array_push(x_101, x_96);
x_103 = l_Nat_reduceBinPred___closed__20;
x_104 = l_Lean_mkAppN(x_103, x_102);
lean_ctor_set(x_33, 0, x_104);
x_105 = l_Nat_reduceBinPred___closed__17;
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_33);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_21, 0, x_108);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_21);
lean_ctor_set(x_109, 1, x_97);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_44);
lean_free_object(x_33);
lean_free_object(x_21);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_82);
if (x_110 == 0)
{
return x_82;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_82, 0);
x_112 = lean_ctor_get(x_82, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_82);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_free_object(x_33);
lean_dec(x_42);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_43);
if (x_114 == 0)
{
return x_43;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_43, 0);
x_116 = lean_ctor_get(x_43, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_43);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_33, 0);
lean_inc(x_118);
lean_dec(x_33);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_119 = l_Lean_Meta_mkDecide(x_4, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_apply_2(x_3, x_30, x_118);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Nat_reduceBinPred___closed__4;
x_125 = l_Lean_Meta_mkEqRefl(x_124, x_8, x_9, x_10, x_11, x_121);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = l_Lean_Expr_appArg_x21(x_120);
lean_dec(x_120);
x_130 = l_Nat_reduceBinPred___closed__11;
x_131 = lean_array_push(x_130, x_4);
x_132 = lean_array_push(x_131, x_129);
x_133 = lean_array_push(x_132, x_126);
x_134 = l_Nat_reduceBinPred___closed__10;
x_135 = l_Lean_mkAppN(x_134, x_133);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_Nat_reduceBinPred___closed__7;
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_21, 0, x_140);
if (lean_is_scalar(x_128)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_128;
}
lean_ctor_set(x_141, 0, x_21);
lean_ctor_set(x_141, 1, x_127);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_120);
lean_free_object(x_21);
lean_dec(x_4);
x_142 = lean_ctor_get(x_125, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_125, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_144 = x_125;
} else {
 lean_dec_ref(x_125);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Nat_reduceBinPred___closed__14;
x_147 = l_Lean_Meta_mkEqRefl(x_146, x_8, x_9, x_10, x_11, x_121);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = l_Lean_Expr_appArg_x21(x_120);
lean_dec(x_120);
x_152 = l_Nat_reduceBinPred___closed__11;
x_153 = lean_array_push(x_152, x_4);
x_154 = lean_array_push(x_153, x_151);
x_155 = lean_array_push(x_154, x_148);
x_156 = l_Nat_reduceBinPred___closed__20;
x_157 = l_Lean_mkAppN(x_156, x_155);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Nat_reduceBinPred___closed__17;
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_158);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_21, 0, x_162);
if (lean_is_scalar(x_150)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_150;
}
lean_ctor_set(x_163, 0, x_21);
lean_ctor_set(x_163, 1, x_149);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_120);
lean_free_object(x_21);
lean_dec(x_4);
x_164 = lean_ctor_get(x_147, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_147, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_166 = x_147;
} else {
 lean_dec_ref(x_147);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_118);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_168 = lean_ctor_get(x_119, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_119, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_170 = x_119;
} else {
 lean_dec_ref(x_119);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
else
{
uint8_t x_172; 
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_172 = !lean_is_exclusive(x_32);
if (x_172 == 0)
{
return x_32;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_32, 0);
x_174 = lean_ctor_get(x_32, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_32);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_21, 0);
lean_inc(x_176);
lean_dec(x_21);
x_177 = l_Lean_Expr_appArg_x21(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_178 = l_Nat_fromExpr_x3f(x_177, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_176);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
lean_dec(x_178);
x_185 = lean_ctor_get(x_179, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_186 = x_179;
} else {
 lean_dec_ref(x_179);
 x_186 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_187 = l_Lean_Meta_mkDecide(x_4, x_8, x_9, x_10, x_11, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_apply_2(x_3, x_176, x_185);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Nat_reduceBinPred___closed__4;
x_193 = l_Lean_Meta_mkEqRefl(x_192, x_8, x_9, x_10, x_11, x_189);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Expr_appArg_x21(x_188);
lean_dec(x_188);
x_198 = l_Nat_reduceBinPred___closed__11;
x_199 = lean_array_push(x_198, x_4);
x_200 = lean_array_push(x_199, x_197);
x_201 = lean_array_push(x_200, x_194);
x_202 = l_Nat_reduceBinPred___closed__10;
x_203 = l_Lean_mkAppN(x_202, x_201);
if (lean_is_scalar(x_186)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_186;
}
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Nat_reduceBinPred___closed__7;
x_206 = lean_unsigned_to_nat(0u);
x_207 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_204);
lean_ctor_set(x_207, 2, x_206);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
if (lean_is_scalar(x_196)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_196;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_195);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_4);
x_211 = lean_ctor_get(x_193, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_213 = x_193;
} else {
 lean_dec_ref(x_193);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = l_Nat_reduceBinPred___closed__14;
x_216 = l_Lean_Meta_mkEqRefl(x_215, x_8, x_9, x_10, x_11, x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Expr_appArg_x21(x_188);
lean_dec(x_188);
x_221 = l_Nat_reduceBinPred___closed__11;
x_222 = lean_array_push(x_221, x_4);
x_223 = lean_array_push(x_222, x_220);
x_224 = lean_array_push(x_223, x_217);
x_225 = l_Nat_reduceBinPred___closed__20;
x_226 = l_Lean_mkAppN(x_225, x_224);
if (lean_is_scalar(x_186)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_186;
}
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Nat_reduceBinPred___closed__17;
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_229);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
if (lean_is_scalar(x_219)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_219;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_218);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_4);
x_234 = lean_ctor_get(x_216, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_216, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_176);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_238 = lean_ctor_get(x_187, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_187, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_240 = x_187;
} else {
 lean_dec_ref(x_187);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_176);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_242 = lean_ctor_get(x_178, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_178, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_244 = x_178;
} else {
 lean_dec_ref(x_178);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_246 = !lean_is_exclusive(x_20);
if (x_246 == 0)
{
return x_20;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_20, 0);
x_248 = lean_ctor_get(x_20, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_20);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Nat_reduceSucc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSucc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSucc___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceSucc___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceSucc___closed__3;
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
x_16 = l_Nat_fromExpr_x3f(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
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
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_nat_add(x_27, x_11);
lean_dec(x_27);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = lean_box(0);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_17, 0, x_33);
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_nat_add(x_34, x_11);
lean_dec(x_34);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_44 = x_17;
} else {
 lean_dec_ref(x_17);
 x_44 = lean_box(0);
}
x_45 = lean_nat_add(x_43, x_11);
lean_dec(x_43);
x_46 = l_Lean_mkNatLit(x_45);
x_47 = lean_box(0);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_16);
if (x_53 == 0)
{
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSucc", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__3;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2;
x_3 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6;
x_4 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_410_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceAdd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceAdd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceAdd___closed__1;
x_2 = l_Nat_reduceAdd___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceAdd___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_add(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_add(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_add(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceAdd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceAdd___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceSucc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2;
x_3 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13;
x_4 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_448_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMul", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMul___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMul", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMul___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceMul___closed__1;
x_2 = l_Nat_reduceMul___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceMul___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_mul(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_mul(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_mul(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMul", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceMul___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2;
x_3 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10;
x_4 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_486_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HSub", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSub___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hSub", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSub___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSub___closed__1;
x_2 = l_Nat_reduceSub___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceSub___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_sub(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_sub(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_sub(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSub", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSub___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10;
x_4 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_524_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HDiv", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceDiv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hDiv", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceDiv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceDiv___closed__1;
x_2 = l_Nat_reduceDiv___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceDiv___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_div(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_div(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_div(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceDiv", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceDiv___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2;
x_3 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10;
x_4 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_562_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMod", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMod___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMod", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMod___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceMod___closed__1;
x_2 = l_Nat_reduceMod___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceMod___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_mod(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_mod(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_mod(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMod", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceMod___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2;
x_3 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10;
x_4 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_600_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reducePow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HPow", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hPow", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reducePow___closed__1;
x_2 = l_Nat_reducePow___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reducePow___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_pow(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_pow(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_pow(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reducePow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reducePow", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reducePow___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2;
x_3 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10;
x_4 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_638_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceGcd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("gcd", 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGcd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceGcd___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceGcd___closed__2;
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_13 = x_76;
x_14 = x_9;
goto block_75;
}
else
{
lean_object* x_77; 
x_77 = l_Nat_reduceBin___closed__1;
x_13 = x_77;
x_14 = x_9;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Nat_fromExpr_x3f(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_nat_gcd(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_gcd(x_28, x_48);
lean_dec(x_48);
lean_dec(x_28);
x_50 = l_Lean_mkNatLit(x_49);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_30, 0, x_55);
return x_30;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_58 = x_31;
} else {
 lean_dec_ref(x_31);
 x_58 = lean_box(0);
}
x_59 = lean_nat_gcd(x_28, x_57);
lean_dec(x_57);
lean_dec(x_28);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
return x_19;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGcd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGcd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceGcd___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___closed__11;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2;
x_3 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6;
x_4 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_657_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceLT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLT___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLT___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceLT___closed__1;
x_2 = l_Nat_reduceLT___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceLT___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_13 = x_247;
x_14 = x_9;
goto block_246;
}
else
{
lean_object* x_248; 
x_248 = l_Nat_reduceBin___closed__1;
x_13 = x_248;
x_14 = x_9;
goto block_246;
}
block_246:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Nat_fromExpr_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_dec_lt(x_29, x_41);
lean_dec(x_41);
lean_dec(x_29);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Nat_reduceBinPred___closed__4;
x_47 = l_Lean_Meta_mkEqRefl(x_46, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_51 = l_Nat_reduceBinPred___closed__11;
x_52 = lean_array_push(x_51, x_1);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_array_push(x_53, x_49);
x_55 = l_Nat_reduceBinPred___closed__10;
x_56 = l_Lean_mkAppN(x_55, x_54);
lean_ctor_set(x_32, 0, x_56);
x_57 = l_Nat_reduceBinPred___closed__7;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_20, 0, x_60);
lean_ctor_set(x_47, 0, x_20);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_64 = l_Nat_reduceBinPred___closed__11;
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_array_push(x_66, x_61);
x_68 = l_Nat_reduceBinPred___closed__10;
x_69 = l_Lean_mkAppN(x_68, x_67);
lean_ctor_set(x_32, 0, x_69);
x_70 = l_Nat_reduceBinPred___closed__7;
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_32);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_20, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Nat_reduceBinPred___closed__14;
x_80 = l_Lean_Meta_mkEqRefl(x_79, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_84 = l_Nat_reduceBinPred___closed__11;
x_85 = lean_array_push(x_84, x_1);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_82);
x_88 = l_Nat_reduceBinPred___closed__20;
x_89 = l_Lean_mkAppN(x_88, x_87);
lean_ctor_set(x_32, 0, x_89);
x_90 = l_Nat_reduceBinPred___closed__17;
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_20, 0, x_93);
lean_ctor_set(x_80, 0, x_20);
return x_80;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_80, 0);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_80);
x_96 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_97 = l_Nat_reduceBinPred___closed__11;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_94);
x_101 = l_Nat_reduceBinPred___closed__20;
x_102 = l_Lean_mkAppN(x_101, x_100);
lean_ctor_set(x_32, 0, x_102);
x_103 = l_Nat_reduceBinPred___closed__17;
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_32);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_20, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_20);
lean_ctor_set(x_107, 1, x_95);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_80);
if (x_108 == 0)
{
return x_80;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_80, 0);
x_110 = lean_ctor_get(x_80, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_80);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_32);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_42);
if (x_112 == 0)
{
return x_42;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_42, 0);
x_114 = lean_ctor_get(x_42, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_42);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_32, 0);
lean_inc(x_116);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_dec_lt(x_29, x_116);
lean_dec(x_116);
lean_dec(x_29);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Nat_reduceBinPred___closed__4;
x_122 = l_Lean_Meta_mkEqRefl(x_121, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_127 = l_Nat_reduceBinPred___closed__11;
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_126);
x_130 = lean_array_push(x_129, x_123);
x_131 = l_Nat_reduceBinPred___closed__10;
x_132 = l_Lean_mkAppN(x_131, x_130);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Nat_reduceBinPred___closed__7;
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_20, 0, x_137);
if (lean_is_scalar(x_125)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_125;
}
lean_ctor_set(x_138, 0, x_20);
lean_ctor_set(x_138, 1, x_124);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Nat_reduceBinPred___closed__14;
x_144 = l_Lean_Meta_mkEqRefl(x_143, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_149 = l_Nat_reduceBinPred___closed__11;
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_array_push(x_151, x_145);
x_153 = l_Nat_reduceBinPred___closed__20;
x_154 = l_Lean_mkAppN(x_153, x_152);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Nat_reduceBinPred___closed__17;
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_20, 0, x_159);
if (lean_is_scalar(x_147)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_147;
}
lean_ctor_set(x_160, 0, x_20);
lean_ctor_set(x_160, 1, x_146);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_116);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_165 = lean_ctor_get(x_117, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
}
else
{
uint8_t x_169; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_31);
if (x_169 == 0)
{
return x_31;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_31, 0);
x_171 = lean_ctor_get(x_31, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_31);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_20, 0);
lean_inc(x_173);
lean_dec(x_20);
x_174 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_175 = l_Nat_fromExpr_x3f(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
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
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_184 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_dec_lt(x_173, x_182);
lean_dec(x_182);
lean_dec(x_173);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Nat_reduceBinPred___closed__4;
x_189 = l_Lean_Meta_mkEqRefl(x_188, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_194 = l_Nat_reduceBinPred___closed__11;
x_195 = lean_array_push(x_194, x_1);
x_196 = lean_array_push(x_195, x_193);
x_197 = lean_array_push(x_196, x_190);
x_198 = l_Nat_reduceBinPred___closed__10;
x_199 = l_Lean_mkAppN(x_198, x_197);
if (lean_is_scalar(x_183)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_183;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Nat_reduceBinPred___closed__7;
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_203, 2, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_207 = lean_ctor_get(x_189, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_209 = x_189;
} else {
 lean_dec_ref(x_189);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Nat_reduceBinPred___closed__14;
x_212 = l_Lean_Meta_mkEqRefl(x_211, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
x_216 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_217 = l_Nat_reduceBinPred___closed__11;
x_218 = lean_array_push(x_217, x_1);
x_219 = lean_array_push(x_218, x_216);
x_220 = lean_array_push(x_219, x_213);
x_221 = l_Nat_reduceBinPred___closed__20;
x_222 = l_Lean_mkAppN(x_221, x_220);
if (lean_is_scalar(x_183)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_183;
}
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Nat_reduceBinPred___closed__17;
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
if (lean_is_scalar(x_215)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_215;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_214);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_212, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_232 = x_212;
} else {
 lean_dec_ref(x_212);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_184, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_184, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_236 = x_184;
} else {
 lean_dec_ref(x_184);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_238 = lean_ctor_get(x_175, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_175, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_240 = x_175;
} else {
 lean_dec_ref(x_175);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_19);
if (x_242 == 0)
{
return x_19;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_19, 0);
x_244 = lean_ctor_get(x_19, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_19);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceLT___closed__3;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9;
x_4 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_696_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceLE___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LE", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLE___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLE___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceLE___closed__1;
x_2 = l_Nat_reduceLE___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceLE___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_13 = x_247;
x_14 = x_9;
goto block_246;
}
else
{
lean_object* x_248; 
x_248 = l_Nat_reduceBin___closed__1;
x_13 = x_248;
x_14 = x_9;
goto block_246;
}
block_246:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Nat_fromExpr_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_dec_le(x_29, x_41);
lean_dec(x_41);
lean_dec(x_29);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Nat_reduceBinPred___closed__4;
x_47 = l_Lean_Meta_mkEqRefl(x_46, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_51 = l_Nat_reduceBinPred___closed__11;
x_52 = lean_array_push(x_51, x_1);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_array_push(x_53, x_49);
x_55 = l_Nat_reduceBinPred___closed__10;
x_56 = l_Lean_mkAppN(x_55, x_54);
lean_ctor_set(x_32, 0, x_56);
x_57 = l_Nat_reduceBinPred___closed__7;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_20, 0, x_60);
lean_ctor_set(x_47, 0, x_20);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_64 = l_Nat_reduceBinPred___closed__11;
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_array_push(x_66, x_61);
x_68 = l_Nat_reduceBinPred___closed__10;
x_69 = l_Lean_mkAppN(x_68, x_67);
lean_ctor_set(x_32, 0, x_69);
x_70 = l_Nat_reduceBinPred___closed__7;
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_32);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_20, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Nat_reduceBinPred___closed__14;
x_80 = l_Lean_Meta_mkEqRefl(x_79, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_84 = l_Nat_reduceBinPred___closed__11;
x_85 = lean_array_push(x_84, x_1);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_82);
x_88 = l_Nat_reduceBinPred___closed__20;
x_89 = l_Lean_mkAppN(x_88, x_87);
lean_ctor_set(x_32, 0, x_89);
x_90 = l_Nat_reduceBinPred___closed__17;
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_20, 0, x_93);
lean_ctor_set(x_80, 0, x_20);
return x_80;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_80, 0);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_80);
x_96 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_97 = l_Nat_reduceBinPred___closed__11;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_94);
x_101 = l_Nat_reduceBinPred___closed__20;
x_102 = l_Lean_mkAppN(x_101, x_100);
lean_ctor_set(x_32, 0, x_102);
x_103 = l_Nat_reduceBinPred___closed__17;
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_32);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_20, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_20);
lean_ctor_set(x_107, 1, x_95);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_80);
if (x_108 == 0)
{
return x_80;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_80, 0);
x_110 = lean_ctor_get(x_80, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_80);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_32);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_42);
if (x_112 == 0)
{
return x_42;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_42, 0);
x_114 = lean_ctor_get(x_42, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_42);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_32, 0);
lean_inc(x_116);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_dec_le(x_29, x_116);
lean_dec(x_116);
lean_dec(x_29);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Nat_reduceBinPred___closed__4;
x_122 = l_Lean_Meta_mkEqRefl(x_121, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_127 = l_Nat_reduceBinPred___closed__11;
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_126);
x_130 = lean_array_push(x_129, x_123);
x_131 = l_Nat_reduceBinPred___closed__10;
x_132 = l_Lean_mkAppN(x_131, x_130);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Nat_reduceBinPred___closed__7;
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_20, 0, x_137);
if (lean_is_scalar(x_125)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_125;
}
lean_ctor_set(x_138, 0, x_20);
lean_ctor_set(x_138, 1, x_124);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Nat_reduceBinPred___closed__14;
x_144 = l_Lean_Meta_mkEqRefl(x_143, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_149 = l_Nat_reduceBinPred___closed__11;
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_array_push(x_151, x_145);
x_153 = l_Nat_reduceBinPred___closed__20;
x_154 = l_Lean_mkAppN(x_153, x_152);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Nat_reduceBinPred___closed__17;
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_20, 0, x_159);
if (lean_is_scalar(x_147)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_147;
}
lean_ctor_set(x_160, 0, x_20);
lean_ctor_set(x_160, 1, x_146);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_116);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_165 = lean_ctor_get(x_117, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
}
else
{
uint8_t x_169; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_31);
if (x_169 == 0)
{
return x_31;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_31, 0);
x_171 = lean_ctor_get(x_31, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_31);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_20, 0);
lean_inc(x_173);
lean_dec(x_20);
x_174 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_175 = l_Nat_fromExpr_x3f(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
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
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_184 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_dec_le(x_173, x_182);
lean_dec(x_182);
lean_dec(x_173);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Nat_reduceBinPred___closed__4;
x_189 = l_Lean_Meta_mkEqRefl(x_188, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_194 = l_Nat_reduceBinPred___closed__11;
x_195 = lean_array_push(x_194, x_1);
x_196 = lean_array_push(x_195, x_193);
x_197 = lean_array_push(x_196, x_190);
x_198 = l_Nat_reduceBinPred___closed__10;
x_199 = l_Lean_mkAppN(x_198, x_197);
if (lean_is_scalar(x_183)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_183;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Nat_reduceBinPred___closed__7;
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_203, 2, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_207 = lean_ctor_get(x_189, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_209 = x_189;
} else {
 lean_dec_ref(x_189);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Nat_reduceBinPred___closed__14;
x_212 = l_Lean_Meta_mkEqRefl(x_211, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
x_216 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_217 = l_Nat_reduceBinPred___closed__11;
x_218 = lean_array_push(x_217, x_1);
x_219 = lean_array_push(x_218, x_216);
x_220 = lean_array_push(x_219, x_213);
x_221 = l_Nat_reduceBinPred___closed__20;
x_222 = l_Lean_mkAppN(x_221, x_220);
if (lean_is_scalar(x_183)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_183;
}
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Nat_reduceBinPred___closed__17;
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
if (lean_is_scalar(x_215)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_215;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_214);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_212, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_232 = x_212;
} else {
 lean_dec_ref(x_212);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_184, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_184, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_236 = x_184;
} else {
 lean_dec_ref(x_184);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_238 = lean_ctor_get(x_175, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_175, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_240 = x_175;
} else {
 lean_dec_ref(x_175);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_19);
if (x_242 == 0)
{
return x_19;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_19, 0);
x_244 = lean_ctor_get(x_19, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_19);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceLE___closed__3;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLE___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8;
x_4 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_735_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceGT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GT", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGT___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("gt", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGT___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceGT___closed__1;
x_2 = l_Nat_reduceGT___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceGT___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_13 = x_247;
x_14 = x_9;
goto block_246;
}
else
{
lean_object* x_248; 
x_248 = l_Nat_reduceBin___closed__1;
x_13 = x_248;
x_14 = x_9;
goto block_246;
}
block_246:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Nat_fromExpr_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_dec_lt(x_41, x_29);
lean_dec(x_29);
lean_dec(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Nat_reduceBinPred___closed__4;
x_47 = l_Lean_Meta_mkEqRefl(x_46, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_51 = l_Nat_reduceBinPred___closed__11;
x_52 = lean_array_push(x_51, x_1);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_array_push(x_53, x_49);
x_55 = l_Nat_reduceBinPred___closed__10;
x_56 = l_Lean_mkAppN(x_55, x_54);
lean_ctor_set(x_32, 0, x_56);
x_57 = l_Nat_reduceBinPred___closed__7;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_20, 0, x_60);
lean_ctor_set(x_47, 0, x_20);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_64 = l_Nat_reduceBinPred___closed__11;
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_array_push(x_66, x_61);
x_68 = l_Nat_reduceBinPred___closed__10;
x_69 = l_Lean_mkAppN(x_68, x_67);
lean_ctor_set(x_32, 0, x_69);
x_70 = l_Nat_reduceBinPred___closed__7;
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_32);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_20, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Nat_reduceBinPred___closed__14;
x_80 = l_Lean_Meta_mkEqRefl(x_79, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_84 = l_Nat_reduceBinPred___closed__11;
x_85 = lean_array_push(x_84, x_1);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_82);
x_88 = l_Nat_reduceBinPred___closed__20;
x_89 = l_Lean_mkAppN(x_88, x_87);
lean_ctor_set(x_32, 0, x_89);
x_90 = l_Nat_reduceBinPred___closed__17;
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_20, 0, x_93);
lean_ctor_set(x_80, 0, x_20);
return x_80;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_80, 0);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_80);
x_96 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_97 = l_Nat_reduceBinPred___closed__11;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_94);
x_101 = l_Nat_reduceBinPred___closed__20;
x_102 = l_Lean_mkAppN(x_101, x_100);
lean_ctor_set(x_32, 0, x_102);
x_103 = l_Nat_reduceBinPred___closed__17;
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_32);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_20, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_20);
lean_ctor_set(x_107, 1, x_95);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_80);
if (x_108 == 0)
{
return x_80;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_80, 0);
x_110 = lean_ctor_get(x_80, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_80);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_32);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_42);
if (x_112 == 0)
{
return x_42;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_42, 0);
x_114 = lean_ctor_get(x_42, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_42);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_32, 0);
lean_inc(x_116);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_dec_lt(x_116, x_29);
lean_dec(x_29);
lean_dec(x_116);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Nat_reduceBinPred___closed__4;
x_122 = l_Lean_Meta_mkEqRefl(x_121, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_127 = l_Nat_reduceBinPred___closed__11;
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_126);
x_130 = lean_array_push(x_129, x_123);
x_131 = l_Nat_reduceBinPred___closed__10;
x_132 = l_Lean_mkAppN(x_131, x_130);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Nat_reduceBinPred___closed__7;
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_20, 0, x_137);
if (lean_is_scalar(x_125)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_125;
}
lean_ctor_set(x_138, 0, x_20);
lean_ctor_set(x_138, 1, x_124);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Nat_reduceBinPred___closed__14;
x_144 = l_Lean_Meta_mkEqRefl(x_143, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_149 = l_Nat_reduceBinPred___closed__11;
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_array_push(x_151, x_145);
x_153 = l_Nat_reduceBinPred___closed__20;
x_154 = l_Lean_mkAppN(x_153, x_152);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Nat_reduceBinPred___closed__17;
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_20, 0, x_159);
if (lean_is_scalar(x_147)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_147;
}
lean_ctor_set(x_160, 0, x_20);
lean_ctor_set(x_160, 1, x_146);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_116);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_165 = lean_ctor_get(x_117, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
}
else
{
uint8_t x_169; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_31);
if (x_169 == 0)
{
return x_31;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_31, 0);
x_171 = lean_ctor_get(x_31, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_31);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_20, 0);
lean_inc(x_173);
lean_dec(x_20);
x_174 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_175 = l_Nat_fromExpr_x3f(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
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
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_184 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_dec_lt(x_182, x_173);
lean_dec(x_173);
lean_dec(x_182);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Nat_reduceBinPred___closed__4;
x_189 = l_Lean_Meta_mkEqRefl(x_188, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_194 = l_Nat_reduceBinPred___closed__11;
x_195 = lean_array_push(x_194, x_1);
x_196 = lean_array_push(x_195, x_193);
x_197 = lean_array_push(x_196, x_190);
x_198 = l_Nat_reduceBinPred___closed__10;
x_199 = l_Lean_mkAppN(x_198, x_197);
if (lean_is_scalar(x_183)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_183;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Nat_reduceBinPred___closed__7;
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_203, 2, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_207 = lean_ctor_get(x_189, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_209 = x_189;
} else {
 lean_dec_ref(x_189);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Nat_reduceBinPred___closed__14;
x_212 = l_Lean_Meta_mkEqRefl(x_211, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
x_216 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_217 = l_Nat_reduceBinPred___closed__11;
x_218 = lean_array_push(x_217, x_1);
x_219 = lean_array_push(x_218, x_216);
x_220 = lean_array_push(x_219, x_213);
x_221 = l_Nat_reduceBinPred___closed__20;
x_222 = l_Lean_mkAppN(x_221, x_220);
if (lean_is_scalar(x_183)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_183;
}
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Nat_reduceBinPred___closed__17;
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
if (lean_is_scalar(x_215)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_215;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_214);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_212, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_232 = x_212;
} else {
 lean_dec_ref(x_212);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_184, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_184, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_236 = x_184;
} else {
 lean_dec_ref(x_184);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_238 = lean_ctor_get(x_175, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_175, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_240 = x_175;
} else {
 lean_dec_ref(x_175);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_19);
if (x_242 == 0)
{
return x_19;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_19, 0);
x_244 = lean_ctor_get(x_19, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_19);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9;
x_4 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_774_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Nat_reduceGE___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GE", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGE___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ge", 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGE___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceGE___closed__1;
x_2 = l_Nat_reduceGE___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_reduceGE___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_13 = x_247;
x_14 = x_9;
goto block_246;
}
else
{
lean_object* x_248; 
x_248 = l_Nat_reduceBin___closed__1;
x_13 = x_248;
x_14 = x_9;
goto block_246;
}
block_246:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = l_Lean_Expr_appFn_x21(x_1);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Nat_fromExpr_x3f(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Nat_fromExpr_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_dec_le(x_41, x_29);
lean_dec(x_29);
lean_dec(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Nat_reduceBinPred___closed__4;
x_47 = l_Lean_Meta_mkEqRefl(x_46, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_51 = l_Nat_reduceBinPred___closed__11;
x_52 = lean_array_push(x_51, x_1);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_array_push(x_53, x_49);
x_55 = l_Nat_reduceBinPred___closed__10;
x_56 = l_Lean_mkAppN(x_55, x_54);
lean_ctor_set(x_32, 0, x_56);
x_57 = l_Nat_reduceBinPred___closed__7;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_20, 0, x_60);
lean_ctor_set(x_47, 0, x_20);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_64 = l_Nat_reduceBinPred___closed__11;
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_array_push(x_66, x_61);
x_68 = l_Nat_reduceBinPred___closed__10;
x_69 = l_Lean_mkAppN(x_68, x_67);
lean_ctor_set(x_32, 0, x_69);
x_70 = l_Nat_reduceBinPred___closed__7;
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_32);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_20, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Nat_reduceBinPred___closed__14;
x_80 = l_Lean_Meta_mkEqRefl(x_79, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_84 = l_Nat_reduceBinPred___closed__11;
x_85 = lean_array_push(x_84, x_1);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_82);
x_88 = l_Nat_reduceBinPred___closed__20;
x_89 = l_Lean_mkAppN(x_88, x_87);
lean_ctor_set(x_32, 0, x_89);
x_90 = l_Nat_reduceBinPred___closed__17;
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_20, 0, x_93);
lean_ctor_set(x_80, 0, x_20);
return x_80;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_80, 0);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_80);
x_96 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
x_97 = l_Nat_reduceBinPred___closed__11;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_94);
x_101 = l_Nat_reduceBinPred___closed__20;
x_102 = l_Lean_mkAppN(x_101, x_100);
lean_ctor_set(x_32, 0, x_102);
x_103 = l_Nat_reduceBinPred___closed__17;
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_32);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_20, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_20);
lean_ctor_set(x_107, 1, x_95);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_80);
if (x_108 == 0)
{
return x_80;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_80, 0);
x_110 = lean_ctor_get(x_80, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_80);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_32);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_42);
if (x_112 == 0)
{
return x_42;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_42, 0);
x_114 = lean_ctor_get(x_42, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_42);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_32, 0);
lean_inc(x_116);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_dec_le(x_116, x_29);
lean_dec(x_29);
lean_dec(x_116);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Nat_reduceBinPred___closed__4;
x_122 = l_Lean_Meta_mkEqRefl(x_121, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_127 = l_Nat_reduceBinPred___closed__11;
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_126);
x_130 = lean_array_push(x_129, x_123);
x_131 = l_Nat_reduceBinPred___closed__10;
x_132 = l_Lean_mkAppN(x_131, x_130);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Nat_reduceBinPred___closed__7;
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_20, 0, x_137);
if (lean_is_scalar(x_125)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_125;
}
lean_ctor_set(x_138, 0, x_20);
lean_ctor_set(x_138, 1, x_124);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Nat_reduceBinPred___closed__14;
x_144 = l_Lean_Meta_mkEqRefl(x_143, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_149 = l_Nat_reduceBinPred___closed__11;
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_148);
x_152 = lean_array_push(x_151, x_145);
x_153 = l_Nat_reduceBinPred___closed__20;
x_154 = l_Lean_mkAppN(x_153, x_152);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Nat_reduceBinPred___closed__17;
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_20, 0, x_159);
if (lean_is_scalar(x_147)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_147;
}
lean_ctor_set(x_160, 0, x_20);
lean_ctor_set(x_160, 1, x_146);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_118);
lean_free_object(x_20);
lean_dec(x_1);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_163 = x_144;
} else {
 lean_dec_ref(x_144);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_116);
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_165 = lean_ctor_get(x_117, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
}
else
{
uint8_t x_169; 
lean_free_object(x_20);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_31);
if (x_169 == 0)
{
return x_31;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_31, 0);
x_171 = lean_ctor_get(x_31, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_31);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_20, 0);
lean_inc(x_173);
lean_dec(x_20);
x_174 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_175 = l_Nat_fromExpr_x3f(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
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
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_184 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_dec_le(x_182, x_173);
lean_dec(x_173);
lean_dec(x_182);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Nat_reduceBinPred___closed__4;
x_189 = l_Lean_Meta_mkEqRefl(x_188, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_194 = l_Nat_reduceBinPred___closed__11;
x_195 = lean_array_push(x_194, x_1);
x_196 = lean_array_push(x_195, x_193);
x_197 = lean_array_push(x_196, x_190);
x_198 = l_Nat_reduceBinPred___closed__10;
x_199 = l_Lean_mkAppN(x_198, x_197);
if (lean_is_scalar(x_183)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_183;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Nat_reduceBinPred___closed__7;
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_203, 2, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_207 = lean_ctor_get(x_189, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_209 = x_189;
} else {
 lean_dec_ref(x_189);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Nat_reduceBinPred___closed__14;
x_212 = l_Lean_Meta_mkEqRefl(x_211, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
x_216 = l_Lean_Expr_appArg_x21(x_185);
lean_dec(x_185);
x_217 = l_Nat_reduceBinPred___closed__11;
x_218 = lean_array_push(x_217, x_1);
x_219 = lean_array_push(x_218, x_216);
x_220 = lean_array_push(x_219, x_213);
x_221 = l_Nat_reduceBinPred___closed__20;
x_222 = l_Lean_mkAppN(x_221, x_220);
if (lean_is_scalar(x_183)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_183;
}
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Nat_reduceBinPred___closed__17;
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
if (lean_is_scalar(x_215)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_215;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_214);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_1);
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_212, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_232 = x_212;
} else {
 lean_dec_ref(x_212);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_184, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_184, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_236 = x_184;
} else {
 lean_dec_ref(x_184);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_238 = lean_ctor_get(x_175, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_175, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_240 = x_175;
} else {
 lean_dec_ref(x_175);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_19);
if (x_242 == 0)
{
return x_19;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_19, 0);
x_244 = lean_ctor_get(x_19, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_19);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGE___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8;
x_4 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_813_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_reduceBin___closed__1 = _init_l_Nat_reduceBin___closed__1();
lean_mark_persistent(l_Nat_reduceBin___closed__1);
l_Nat_reduceBinPred___closed__1 = _init_l_Nat_reduceBinPred___closed__1();
lean_mark_persistent(l_Nat_reduceBinPred___closed__1);
l_Nat_reduceBinPred___closed__2 = _init_l_Nat_reduceBinPred___closed__2();
lean_mark_persistent(l_Nat_reduceBinPred___closed__2);
l_Nat_reduceBinPred___closed__3 = _init_l_Nat_reduceBinPred___closed__3();
lean_mark_persistent(l_Nat_reduceBinPred___closed__3);
l_Nat_reduceBinPred___closed__4 = _init_l_Nat_reduceBinPred___closed__4();
lean_mark_persistent(l_Nat_reduceBinPred___closed__4);
l_Nat_reduceBinPred___closed__5 = _init_l_Nat_reduceBinPred___closed__5();
lean_mark_persistent(l_Nat_reduceBinPred___closed__5);
l_Nat_reduceBinPred___closed__6 = _init_l_Nat_reduceBinPred___closed__6();
lean_mark_persistent(l_Nat_reduceBinPred___closed__6);
l_Nat_reduceBinPred___closed__7 = _init_l_Nat_reduceBinPred___closed__7();
lean_mark_persistent(l_Nat_reduceBinPred___closed__7);
l_Nat_reduceBinPred___closed__8 = _init_l_Nat_reduceBinPred___closed__8();
lean_mark_persistent(l_Nat_reduceBinPred___closed__8);
l_Nat_reduceBinPred___closed__9 = _init_l_Nat_reduceBinPred___closed__9();
lean_mark_persistent(l_Nat_reduceBinPred___closed__9);
l_Nat_reduceBinPred___closed__10 = _init_l_Nat_reduceBinPred___closed__10();
lean_mark_persistent(l_Nat_reduceBinPred___closed__10);
l_Nat_reduceBinPred___closed__11 = _init_l_Nat_reduceBinPred___closed__11();
lean_mark_persistent(l_Nat_reduceBinPred___closed__11);
l_Nat_reduceBinPred___closed__12 = _init_l_Nat_reduceBinPred___closed__12();
lean_mark_persistent(l_Nat_reduceBinPred___closed__12);
l_Nat_reduceBinPred___closed__13 = _init_l_Nat_reduceBinPred___closed__13();
lean_mark_persistent(l_Nat_reduceBinPred___closed__13);
l_Nat_reduceBinPred___closed__14 = _init_l_Nat_reduceBinPred___closed__14();
lean_mark_persistent(l_Nat_reduceBinPred___closed__14);
l_Nat_reduceBinPred___closed__15 = _init_l_Nat_reduceBinPred___closed__15();
lean_mark_persistent(l_Nat_reduceBinPred___closed__15);
l_Nat_reduceBinPred___closed__16 = _init_l_Nat_reduceBinPred___closed__16();
lean_mark_persistent(l_Nat_reduceBinPred___closed__16);
l_Nat_reduceBinPred___closed__17 = _init_l_Nat_reduceBinPred___closed__17();
lean_mark_persistent(l_Nat_reduceBinPred___closed__17);
l_Nat_reduceBinPred___closed__18 = _init_l_Nat_reduceBinPred___closed__18();
lean_mark_persistent(l_Nat_reduceBinPred___closed__18);
l_Nat_reduceBinPred___closed__19 = _init_l_Nat_reduceBinPred___closed__19();
lean_mark_persistent(l_Nat_reduceBinPred___closed__19);
l_Nat_reduceBinPred___closed__20 = _init_l_Nat_reduceBinPred___closed__20();
lean_mark_persistent(l_Nat_reduceBinPred___closed__20);
l_Nat_reduceSucc___closed__1 = _init_l_Nat_reduceSucc___closed__1();
lean_mark_persistent(l_Nat_reduceSucc___closed__1);
l_Nat_reduceSucc___closed__2 = _init_l_Nat_reduceSucc___closed__2();
lean_mark_persistent(l_Nat_reduceSucc___closed__2);
l_Nat_reduceSucc___closed__3 = _init_l_Nat_reduceSucc___closed__3();
lean_mark_persistent(l_Nat_reduceSucc___closed__3);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__1);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__2);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__3);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__4);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__5);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__6);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_408_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_410_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceAdd___closed__1 = _init_l_Nat_reduceAdd___closed__1();
lean_mark_persistent(l_Nat_reduceAdd___closed__1);
l_Nat_reduceAdd___closed__2 = _init_l_Nat_reduceAdd___closed__2();
lean_mark_persistent(l_Nat_reduceAdd___closed__2);
l_Nat_reduceAdd___closed__3 = _init_l_Nat_reduceAdd___closed__3();
lean_mark_persistent(l_Nat_reduceAdd___closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__1);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__2);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__4);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__5);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__6);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__7);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__8);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__9);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__10);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__11);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__12);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__13);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446____closed__14);
if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_446_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_448_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMul___closed__1 = _init_l_Nat_reduceMul___closed__1();
lean_mark_persistent(l_Nat_reduceMul___closed__1);
l_Nat_reduceMul___closed__2 = _init_l_Nat_reduceMul___closed__2();
lean_mark_persistent(l_Nat_reduceMul___closed__2);
l_Nat_reduceMul___closed__3 = _init_l_Nat_reduceMul___closed__3();
lean_mark_persistent(l_Nat_reduceMul___closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__1);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__2);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__4);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__5);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__6);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__7);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__8);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__9);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__10);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_484_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_486_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceSub___closed__1 = _init_l_Nat_reduceSub___closed__1();
lean_mark_persistent(l_Nat_reduceSub___closed__1);
l_Nat_reduceSub___closed__2 = _init_l_Nat_reduceSub___closed__2();
lean_mark_persistent(l_Nat_reduceSub___closed__2);
l_Nat_reduceSub___closed__3 = _init_l_Nat_reduceSub___closed__3();
lean_mark_persistent(l_Nat_reduceSub___closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__1);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__2);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__4);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__5);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__6);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__7);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__8);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__9);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__10);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_522_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_524_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceDiv___closed__1 = _init_l_Nat_reduceDiv___closed__1();
lean_mark_persistent(l_Nat_reduceDiv___closed__1);
l_Nat_reduceDiv___closed__2 = _init_l_Nat_reduceDiv___closed__2();
lean_mark_persistent(l_Nat_reduceDiv___closed__2);
l_Nat_reduceDiv___closed__3 = _init_l_Nat_reduceDiv___closed__3();
lean_mark_persistent(l_Nat_reduceDiv___closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__1);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__2);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__4);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__5);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__6);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__7);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__8);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__9);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__10);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_560_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_562_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMod___closed__1 = _init_l_Nat_reduceMod___closed__1();
lean_mark_persistent(l_Nat_reduceMod___closed__1);
l_Nat_reduceMod___closed__2 = _init_l_Nat_reduceMod___closed__2();
lean_mark_persistent(l_Nat_reduceMod___closed__2);
l_Nat_reduceMod___closed__3 = _init_l_Nat_reduceMod___closed__3();
lean_mark_persistent(l_Nat_reduceMod___closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__1);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__2);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__4);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__5);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__6);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__7);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__8);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__9);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__10);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_598_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_600_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reducePow___closed__1 = _init_l_Nat_reducePow___closed__1();
lean_mark_persistent(l_Nat_reducePow___closed__1);
l_Nat_reducePow___closed__2 = _init_l_Nat_reducePow___closed__2();
lean_mark_persistent(l_Nat_reducePow___closed__2);
l_Nat_reducePow___closed__3 = _init_l_Nat_reducePow___closed__3();
lean_mark_persistent(l_Nat_reducePow___closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__1);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__2);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__4);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__5);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__6);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__7);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__8);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__9);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__10);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_636_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_638_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGcd___closed__1 = _init_l_Nat_reduceGcd___closed__1();
lean_mark_persistent(l_Nat_reduceGcd___closed__1);
l_Nat_reduceGcd___closed__2 = _init_l_Nat_reduceGcd___closed__2();
lean_mark_persistent(l_Nat_reduceGcd___closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__1);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__3);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__4);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__5);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__6);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_655_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_657_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLT___closed__1 = _init_l_Nat_reduceLT___closed__1();
lean_mark_persistent(l_Nat_reduceLT___closed__1);
l_Nat_reduceLT___closed__2 = _init_l_Nat_reduceLT___closed__2();
lean_mark_persistent(l_Nat_reduceLT___closed__2);
l_Nat_reduceLT___closed__3 = _init_l_Nat_reduceLT___closed__3();
lean_mark_persistent(l_Nat_reduceLT___closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__1);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__2);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__4);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__5);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__6);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__7);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__8);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__9);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694____closed__10);
if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_694_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_696_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLE___closed__1 = _init_l_Nat_reduceLE___closed__1();
lean_mark_persistent(l_Nat_reduceLE___closed__1);
l_Nat_reduceLE___closed__2 = _init_l_Nat_reduceLE___closed__2();
lean_mark_persistent(l_Nat_reduceLE___closed__2);
l_Nat_reduceLE___closed__3 = _init_l_Nat_reduceLE___closed__3();
lean_mark_persistent(l_Nat_reduceLE___closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__1);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__2);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__4);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__5);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__6);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__7);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__8);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733____closed__9);
if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_733_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_735_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGT___closed__1 = _init_l_Nat_reduceGT___closed__1();
lean_mark_persistent(l_Nat_reduceGT___closed__1);
l_Nat_reduceGT___closed__2 = _init_l_Nat_reduceGT___closed__2();
lean_mark_persistent(l_Nat_reduceGT___closed__2);
l_Nat_reduceGT___closed__3 = _init_l_Nat_reduceGT___closed__3();
lean_mark_persistent(l_Nat_reduceGT___closed__3);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__1);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__2);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_772_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_774_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGE___closed__1 = _init_l_Nat_reduceGE___closed__1();
lean_mark_persistent(l_Nat_reduceGE___closed__1);
l_Nat_reduceGE___closed__2 = _init_l_Nat_reduceGE___closed__2();
lean_mark_persistent(l_Nat_reduceGE___closed__2);
l_Nat_reduceGE___closed__3 = _init_l_Nat_reduceGE___closed__3();
lean_mark_persistent(l_Nat_reduceGE___closed__3);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__1);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__2);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_811_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_813_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
