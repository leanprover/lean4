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
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__3;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_880_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSub___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1;
static lean_object* l_Nat_reduceSub___closed__1;
static lean_object* l_Nat_reduceDiv___closed__3;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_841_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782_(lean_object*);
static lean_object* l_Nat_reduceMod___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2;
static lean_object* l_Nat_reduceDiv___closed__2;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_822_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_670_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_632_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_708_(lean_object*);
static lean_object* l_Nat_reduceMul___closed__2;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917_(lean_object*);
static lean_object* l_Nat_reduceDiv___closed__1;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_958_(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995_(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__16;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGE___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839_(lean_object*);
static lean_object* l_Nat_reduceGcd___closed__1;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630_(lean_object*);
static lean_object* l_Nat_reduceLE___closed__1;
static lean_object* l_Nat_reduceSub___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__13;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGT___closed__3;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2;
static lean_object* l_Nat_reduceGT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4;
static lean_object* l_Nat_reduceLT___closed__3;
static lean_object* l_Nat_reduceLT___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_784_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_997_(lean_object*);
static lean_object* l_Nat_reduceLE___closed__3;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Nat_reduceMod___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__20;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__14;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__2;
static lean_object* l_Nat_reduceGE___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4;
static lean_object* l_Nat_reduceSucc___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668_(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__1;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11;
static lean_object* l_Nat_reduceMul___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__15;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__10;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1;
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__19;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGcd___closed__2;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4;
static lean_object* l_Nat_reduceGT___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14;
static lean_object* l_Nat_reduceMod___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_919_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSucc___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744_(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceMul___closed__3;
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_594_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7;
static lean_object* l_Nat_reduceGE___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_746_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6;
static lean_object* l_Nat_reduceLE___closed__2;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8;
static lean_object* l_Nat_reducePow___closed__2;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2;
static lean_object* l_Nat_reduceLT___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__18;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10;
static lean_object* l_Nat_reduceSucc___closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__11;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4;
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
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Nat_fromExpr_x3f(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_apply_1(x_2, x_24);
x_26 = l_Lean_mkNatLit(x_25);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_14, 0, x_30);
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_apply_1(x_2, x_31);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = lean_box(0);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_41 = x_14;
} else {
 lean_dec_ref(x_14);
 x_41 = lean_box(0);
}
x_42 = lean_apply_1(x_2, x_40);
x_43 = l_Lean_mkNatLit(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
lean_dec(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_16 = lean_box(0);
x_17 = l_Nat_reduceUnary___lambda__1(x_4, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Nat_fromExpr_x3f(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Expr_appArg_x21(x_1);
x_25 = l_Nat_fromExpr_x3f(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_apply_2(x_2, x_23, x_36);
x_38 = l_Lean_mkNatLit(x_37);
x_39 = lean_box(0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_26, 0, x_42);
return x_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_apply_2(x_2, x_23, x_43);
x_45 = l_Lean_mkNatLit(x_44);
x_46 = lean_box(0);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_25, 0, x_50);
return x_25;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_dec(x_25);
x_52 = lean_ctor_get(x_26, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_53 = x_26;
} else {
 lean_dec_ref(x_26);
 x_53 = lean_box(0);
}
x_54 = lean_apply_2(x_2, x_23, x_52);
x_55 = l_Lean_mkNatLit(x_54);
x_56 = lean_box(0);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_53;
}
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_23);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
return x_25;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_25, 0);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_25);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
return x_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_14, 0);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_14);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
lean_dec(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_16 = lean_box(0);
x_17 = l_Nat_reduceBin___lambda__1(x_4, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceBin___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_2 = l_Nat_reduceBinPred___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_2 = l_Nat_reduceBinPred___lambda__1___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBinPred___lambda__1___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Nat_fromExpr_x3f(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Nat_fromExpr_x3f(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_37 = l_Lean_Meta_mkDecide(x_1, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_apply_2(x_2, x_24, x_36);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_43 = l_Lean_Meta_mkEqRefl(x_42, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_47 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_48 = lean_array_push(x_47, x_1);
x_49 = lean_array_push(x_48, x_46);
x_50 = lean_array_push(x_49, x_45);
x_51 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_52 = l_Lean_mkAppN(x_51, x_50);
lean_ctor_set(x_27, 0, x_52);
x_53 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_27);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_15, 0, x_56);
lean_ctor_set(x_43, 0, x_15);
return x_43;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_43, 0);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_43);
x_59 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_60 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_61 = lean_array_push(x_60, x_1);
x_62 = lean_array_push(x_61, x_59);
x_63 = lean_array_push(x_62, x_57);
x_64 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_65 = l_Lean_mkAppN(x_64, x_63);
lean_ctor_set(x_27, 0, x_65);
x_66 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_27);
lean_ctor_set(x_68, 2, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_15, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_15);
lean_ctor_set(x_70, 1, x_58);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_38);
lean_free_object(x_27);
lean_free_object(x_15);
lean_dec(x_1);
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
lean_object* x_75; lean_object* x_76; 
x_75 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_76 = l_Lean_Meta_mkEqRefl(x_75, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_80 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_81 = lean_array_push(x_80, x_1);
x_82 = lean_array_push(x_81, x_79);
x_83 = lean_array_push(x_82, x_78);
x_84 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_85 = l_Lean_mkAppN(x_84, x_83);
lean_ctor_set(x_27, 0, x_85);
x_86 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_27);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_15, 0, x_89);
lean_ctor_set(x_76, 0, x_15);
return x_76;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_76, 0);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_76);
x_92 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_93 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_94 = lean_array_push(x_93, x_1);
x_95 = lean_array_push(x_94, x_92);
x_96 = lean_array_push(x_95, x_90);
x_97 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_98 = l_Lean_mkAppN(x_97, x_96);
lean_ctor_set(x_27, 0, x_98);
x_99 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_27);
lean_ctor_set(x_101, 2, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_15, 0, x_102);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_15);
lean_ctor_set(x_103, 1, x_91);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_38);
lean_free_object(x_27);
lean_free_object(x_15);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_76);
if (x_104 == 0)
{
return x_76;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_76, 0);
x_106 = lean_ctor_get(x_76, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_76);
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
uint8_t x_108; 
lean_free_object(x_27);
lean_dec(x_36);
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_37);
if (x_108 == 0)
{
return x_37;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_37, 0);
x_110 = lean_ctor_get(x_37, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_37);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_27, 0);
lean_inc(x_112);
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_113 = l_Lean_Meta_mkDecide(x_1, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_apply_2(x_2, x_24, x_112);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_119 = l_Lean_Meta_mkEqRefl(x_118, x_7, x_8, x_9, x_10, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
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
x_123 = l_Lean_Expr_appArg_x21(x_114);
lean_dec(x_114);
x_124 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_125 = lean_array_push(x_124, x_1);
x_126 = lean_array_push(x_125, x_123);
x_127 = lean_array_push(x_126, x_120);
x_128 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_129 = l_Lean_mkAppN(x_128, x_127);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_133, 2, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_15, 0, x_134);
if (lean_is_scalar(x_122)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_122;
}
lean_ctor_set(x_135, 0, x_15);
lean_ctor_set(x_135, 1, x_121);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_114);
lean_free_object(x_15);
lean_dec(x_1);
x_136 = lean_ctor_get(x_119, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_138 = x_119;
} else {
 lean_dec_ref(x_119);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_141 = l_Lean_Meta_mkEqRefl(x_140, x_7, x_8, x_9, x_10, x_115);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Expr_appArg_x21(x_114);
lean_dec(x_114);
x_146 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_147 = lean_array_push(x_146, x_1);
x_148 = lean_array_push(x_147, x_145);
x_149 = lean_array_push(x_148, x_142);
x_150 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_151 = l_Lean_mkAppN(x_150, x_149);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set(x_155, 2, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_15, 0, x_156);
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_144;
}
lean_ctor_set(x_157, 0, x_15);
lean_ctor_set(x_157, 1, x_143);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_114);
lean_free_object(x_15);
lean_dec(x_1);
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_160 = x_141;
} else {
 lean_dec_ref(x_141);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_112);
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_113, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_113, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_164 = x_113;
} else {
 lean_dec_ref(x_113);
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
}
}
else
{
uint8_t x_166; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_26);
if (x_166 == 0)
{
return x_26;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_26, 0);
x_168 = lean_ctor_get(x_26, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_26);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_15, 0);
lean_inc(x_170);
lean_dec(x_15);
x_171 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_172 = l_Nat_fromExpr_x3f(x_171, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_170);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_180 = x_173;
} else {
 lean_dec_ref(x_173);
 x_180 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_181 = l_Lean_Meta_mkDecide(x_1, x_7, x_8, x_9, x_10, x_178);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_apply_2(x_2, x_170, x_179);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_187 = l_Lean_Meta_mkEqRefl(x_186, x_7, x_8, x_9, x_10, x_183);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = l_Lean_Expr_appArg_x21(x_182);
lean_dec(x_182);
x_192 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_193 = lean_array_push(x_192, x_1);
x_194 = lean_array_push(x_193, x_191);
x_195 = lean_array_push(x_194, x_188);
x_196 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_197 = l_Lean_mkAppN(x_196, x_195);
if (lean_is_scalar(x_180)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_180;
}
lean_ctor_set(x_198, 0, x_197);
x_199 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
if (lean_is_scalar(x_190)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_190;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_189);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_1);
x_205 = lean_ctor_get(x_187, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_187, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_207 = x_187;
} else {
 lean_dec_ref(x_187);
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
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_210 = l_Lean_Meta_mkEqRefl(x_209, x_7, x_8, x_9, x_10, x_183);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Expr_appArg_x21(x_182);
lean_dec(x_182);
x_215 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_216 = lean_array_push(x_215, x_1);
x_217 = lean_array_push(x_216, x_214);
x_218 = lean_array_push(x_217, x_211);
x_219 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_220 = l_Lean_mkAppN(x_219, x_218);
if (lean_is_scalar(x_180)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_180;
}
lean_ctor_set(x_221, 0, x_220);
x_222 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_223);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
if (lean_is_scalar(x_213)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_213;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_212);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_1);
x_228 = lean_ctor_get(x_210, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_210, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_230 = x_210;
} else {
 lean_dec_ref(x_210);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_170);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_232 = lean_ctor_get(x_181, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_181, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_234 = x_181;
} else {
 lean_dec_ref(x_181);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_170);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_ctor_get(x_172, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_172, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_238 = x_172;
} else {
 lean_dec_ref(x_172);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_240 = !lean_is_exclusive(x_14);
if (x_240 == 0)
{
return x_14;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_14, 0);
x_242 = lean_ctor_get(x_14, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_14);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
lean_dec(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_16 = lean_box(0);
x_17 = l_Nat_reduceBinPred___lambda__1(x_4, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceBinPred___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_appArg_x21(x_1);
x_12 = l_Nat_fromExpr_x3f(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_mkNatLit(x_25);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_13, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_12, 0, x_39);
return x_12;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_42 = x_13;
} else {
 lean_dec_ref(x_13);
 x_42 = lean_box(0);
}
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_41, x_43);
lean_dec(x_41);
x_45 = l_Lean_mkNatLit(x_44);
x_46 = lean_box(0);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceSucc___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceSucc___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSucc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSucc", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2;
x_3 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6;
x_4 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_594_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_add(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_add(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_add(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceAdd___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceAdd___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceAdd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceAdd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceSucc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2;
x_3 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13;
x_4 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_632_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_mul(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_mul(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_mul(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceMul___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceMul___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceMul___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMul", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2;
x_3 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10;
x_4 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_670_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_sub(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_sub(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_sub(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceSub___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceSub___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceSub___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSub", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10;
x_4 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_708_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_div(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_div(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_div(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceDiv___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceDiv___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceDiv___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceDiv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceDiv", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2;
x_3 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10;
x_4 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_746_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_mod(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_mod(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_mod(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceMod___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceMod___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceMod___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceMod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMod", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2;
x_3 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10;
x_4 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_784_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_pow(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_pow(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_pow(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reducePow___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reducePow___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reducePow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reducePow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reducePow", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2;
x_3 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10;
x_4 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_822_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Expr_appArg_x21(x_1);
x_24 = l_Nat_fromExpr_x3f(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_gcd(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_gcd(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_24, 0, x_49);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = lean_nat_gcd(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceGcd___closed__2;
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceGcd___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceGcd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceGcd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGcd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2;
x_3 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6;
x_4 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_841_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Nat_fromExpr_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_36 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_nat_dec_lt(x_23, x_35);
lean_dec(x_35);
lean_dec(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_41 = l_Lean_Meta_mkEqRefl(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_45 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_46 = lean_array_push(x_45, x_1);
x_47 = lean_array_push(x_46, x_44);
x_48 = lean_array_push(x_47, x_43);
x_49 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_50 = l_Lean_mkAppN(x_49, x_48);
lean_ctor_set(x_26, 0, x_50);
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_14, 0, x_54);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_58 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_57);
x_61 = lean_array_push(x_60, x_55);
x_62 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_63 = l_Lean_mkAppN(x_62, x_61);
lean_ctor_set(x_26, 0, x_63);
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_26);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_14, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
return x_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 0);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_41);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_74 = l_Lean_Meta_mkEqRefl(x_73, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_78 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_79 = lean_array_push(x_78, x_1);
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_array_push(x_80, x_76);
x_82 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_83 = l_Lean_mkAppN(x_82, x_81);
lean_ctor_set(x_26, 0, x_83);
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_26);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_14, 0, x_87);
lean_ctor_set(x_74, 0, x_14);
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_91 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_array_push(x_93, x_88);
x_95 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_96 = l_Lean_mkAppN(x_95, x_94);
lean_ctor_set(x_26, 0, x_96);
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_26);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_14, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_14);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_74);
if (x_102 == 0)
{
return x_74;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_74, 0);
x_104 = lean_ctor_get(x_74, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_74);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_26);
lean_dec(x_35);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
return x_36;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_36, 0);
x_108 = lean_ctor_get(x_36, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_36);
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
x_110 = lean_ctor_get(x_26, 0);
lean_inc(x_110);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_111 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_nat_dec_lt(x_23, x_110);
lean_dec(x_110);
lean_dec(x_23);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_116 = l_Lean_Meta_mkEqRefl(x_115, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_121 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_120);
x_124 = lean_array_push(x_123, x_117);
x_125 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_126 = l_Lean_mkAppN(x_125, x_124);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_14, 0, x_131);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_119;
}
lean_ctor_set(x_132, 0, x_14);
lean_ctor_set(x_132, 1, x_118);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_143 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_144 = lean_array_push(x_143, x_1);
x_145 = lean_array_push(x_144, x_142);
x_146 = lean_array_push(x_145, x_139);
x_147 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_148 = l_Lean_mkAppN(x_147, x_146);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_14, 0, x_153);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_14);
lean_ctor_set(x_154, 1, x_140);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_157 = x_138;
} else {
 lean_dec_ref(x_138);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_110);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_111, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_111, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_161 = x_111;
} else {
 lean_dec_ref(x_111);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_25);
if (x_163 == 0)
{
return x_25;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_25, 0);
x_165 = lean_ctor_get(x_25, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_25);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_14, 0);
lean_inc(x_167);
lean_dec(x_14);
x_168 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_169 = l_Nat_fromExpr_x3f(x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_178 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_nat_dec_lt(x_167, x_176);
lean_dec(x_176);
lean_dec(x_167);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_183 = l_Lean_Meta_mkEqRefl(x_182, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_188 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_189 = lean_array_push(x_188, x_1);
x_190 = lean_array_push(x_189, x_187);
x_191 = lean_array_push(x_190, x_184);
x_192 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_193 = l_Lean_mkAppN(x_192, x_191);
if (lean_is_scalar(x_177)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_177;
}
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_201 = lean_ctor_get(x_183, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_203 = x_183;
} else {
 lean_dec_ref(x_183);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_206 = l_Lean_Meta_mkEqRefl(x_205, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_211 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_212 = lean_array_push(x_211, x_1);
x_213 = lean_array_push(x_212, x_210);
x_214 = lean_array_push(x_213, x_207);
x_215 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_216 = l_Lean_mkAppN(x_215, x_214);
if (lean_is_scalar(x_177)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_177;
}
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_209)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_209;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_208);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_224 = lean_ctor_get(x_206, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
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
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_178, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_178, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_230 = x_178;
} else {
 lean_dec_ref(x_178);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_169, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_169, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_234 = x_169;
} else {
 lean_dec_ref(x_169);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_13);
if (x_236 == 0)
{
return x_13;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_13, 0);
x_238 = lean_ctor_get(x_13, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_13);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceLT___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceLT___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceLT___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLT), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9;
x_4 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_880_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Nat_fromExpr_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_36 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_nat_dec_le(x_23, x_35);
lean_dec(x_35);
lean_dec(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_41 = l_Lean_Meta_mkEqRefl(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_45 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_46 = lean_array_push(x_45, x_1);
x_47 = lean_array_push(x_46, x_44);
x_48 = lean_array_push(x_47, x_43);
x_49 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_50 = l_Lean_mkAppN(x_49, x_48);
lean_ctor_set(x_26, 0, x_50);
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_14, 0, x_54);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_58 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_57);
x_61 = lean_array_push(x_60, x_55);
x_62 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_63 = l_Lean_mkAppN(x_62, x_61);
lean_ctor_set(x_26, 0, x_63);
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_26);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_14, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
return x_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 0);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_41);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_74 = l_Lean_Meta_mkEqRefl(x_73, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_78 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_79 = lean_array_push(x_78, x_1);
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_array_push(x_80, x_76);
x_82 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_83 = l_Lean_mkAppN(x_82, x_81);
lean_ctor_set(x_26, 0, x_83);
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_26);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_14, 0, x_87);
lean_ctor_set(x_74, 0, x_14);
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_91 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_array_push(x_93, x_88);
x_95 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_96 = l_Lean_mkAppN(x_95, x_94);
lean_ctor_set(x_26, 0, x_96);
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_26);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_14, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_14);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_74);
if (x_102 == 0)
{
return x_74;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_74, 0);
x_104 = lean_ctor_get(x_74, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_74);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_26);
lean_dec(x_35);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
return x_36;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_36, 0);
x_108 = lean_ctor_get(x_36, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_36);
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
x_110 = lean_ctor_get(x_26, 0);
lean_inc(x_110);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_111 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_nat_dec_le(x_23, x_110);
lean_dec(x_110);
lean_dec(x_23);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_116 = l_Lean_Meta_mkEqRefl(x_115, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_121 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_120);
x_124 = lean_array_push(x_123, x_117);
x_125 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_126 = l_Lean_mkAppN(x_125, x_124);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_14, 0, x_131);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_119;
}
lean_ctor_set(x_132, 0, x_14);
lean_ctor_set(x_132, 1, x_118);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_143 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_144 = lean_array_push(x_143, x_1);
x_145 = lean_array_push(x_144, x_142);
x_146 = lean_array_push(x_145, x_139);
x_147 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_148 = l_Lean_mkAppN(x_147, x_146);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_14, 0, x_153);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_14);
lean_ctor_set(x_154, 1, x_140);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_157 = x_138;
} else {
 lean_dec_ref(x_138);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_110);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_111, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_111, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_161 = x_111;
} else {
 lean_dec_ref(x_111);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_25);
if (x_163 == 0)
{
return x_25;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_25, 0);
x_165 = lean_ctor_get(x_25, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_25);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_14, 0);
lean_inc(x_167);
lean_dec(x_14);
x_168 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_169 = l_Nat_fromExpr_x3f(x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_178 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_nat_dec_le(x_167, x_176);
lean_dec(x_176);
lean_dec(x_167);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_183 = l_Lean_Meta_mkEqRefl(x_182, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_188 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_189 = lean_array_push(x_188, x_1);
x_190 = lean_array_push(x_189, x_187);
x_191 = lean_array_push(x_190, x_184);
x_192 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_193 = l_Lean_mkAppN(x_192, x_191);
if (lean_is_scalar(x_177)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_177;
}
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_201 = lean_ctor_get(x_183, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_203 = x_183;
} else {
 lean_dec_ref(x_183);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_206 = l_Lean_Meta_mkEqRefl(x_205, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_211 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_212 = lean_array_push(x_211, x_1);
x_213 = lean_array_push(x_212, x_210);
x_214 = lean_array_push(x_213, x_207);
x_215 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_216 = l_Lean_mkAppN(x_215, x_214);
if (lean_is_scalar(x_177)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_177;
}
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_209)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_209;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_208);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_224 = lean_ctor_get(x_206, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
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
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_178, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_178, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_230 = x_178;
} else {
 lean_dec_ref(x_178);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_169, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_169, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_234 = x_169;
} else {
 lean_dec_ref(x_169);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_13);
if (x_236 == 0)
{
return x_13;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_13, 0);
x_238 = lean_ctor_get(x_13, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_13);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceLE___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceLE___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceLE___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLE), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8;
x_4 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_919_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Nat_fromExpr_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_36 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_nat_dec_lt(x_35, x_23);
lean_dec(x_23);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_41 = l_Lean_Meta_mkEqRefl(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_45 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_46 = lean_array_push(x_45, x_1);
x_47 = lean_array_push(x_46, x_44);
x_48 = lean_array_push(x_47, x_43);
x_49 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_50 = l_Lean_mkAppN(x_49, x_48);
lean_ctor_set(x_26, 0, x_50);
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_14, 0, x_54);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_58 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_57);
x_61 = lean_array_push(x_60, x_55);
x_62 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_63 = l_Lean_mkAppN(x_62, x_61);
lean_ctor_set(x_26, 0, x_63);
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_26);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_14, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
return x_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 0);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_41);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_74 = l_Lean_Meta_mkEqRefl(x_73, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_78 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_79 = lean_array_push(x_78, x_1);
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_array_push(x_80, x_76);
x_82 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_83 = l_Lean_mkAppN(x_82, x_81);
lean_ctor_set(x_26, 0, x_83);
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_26);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_14, 0, x_87);
lean_ctor_set(x_74, 0, x_14);
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_91 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_array_push(x_93, x_88);
x_95 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_96 = l_Lean_mkAppN(x_95, x_94);
lean_ctor_set(x_26, 0, x_96);
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_26);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_14, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_14);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_74);
if (x_102 == 0)
{
return x_74;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_74, 0);
x_104 = lean_ctor_get(x_74, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_74);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_26);
lean_dec(x_35);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
return x_36;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_36, 0);
x_108 = lean_ctor_get(x_36, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_36);
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
x_110 = lean_ctor_get(x_26, 0);
lean_inc(x_110);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_111 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_nat_dec_lt(x_110, x_23);
lean_dec(x_23);
lean_dec(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_116 = l_Lean_Meta_mkEqRefl(x_115, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_121 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_120);
x_124 = lean_array_push(x_123, x_117);
x_125 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_126 = l_Lean_mkAppN(x_125, x_124);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_14, 0, x_131);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_119;
}
lean_ctor_set(x_132, 0, x_14);
lean_ctor_set(x_132, 1, x_118);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_143 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_144 = lean_array_push(x_143, x_1);
x_145 = lean_array_push(x_144, x_142);
x_146 = lean_array_push(x_145, x_139);
x_147 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_148 = l_Lean_mkAppN(x_147, x_146);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_14, 0, x_153);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_14);
lean_ctor_set(x_154, 1, x_140);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_157 = x_138;
} else {
 lean_dec_ref(x_138);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_110);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_111, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_111, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_161 = x_111;
} else {
 lean_dec_ref(x_111);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_25);
if (x_163 == 0)
{
return x_25;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_25, 0);
x_165 = lean_ctor_get(x_25, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_25);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_14, 0);
lean_inc(x_167);
lean_dec(x_14);
x_168 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_169 = l_Nat_fromExpr_x3f(x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_178 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_nat_dec_lt(x_176, x_167);
lean_dec(x_167);
lean_dec(x_176);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_183 = l_Lean_Meta_mkEqRefl(x_182, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_188 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_189 = lean_array_push(x_188, x_1);
x_190 = lean_array_push(x_189, x_187);
x_191 = lean_array_push(x_190, x_184);
x_192 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_193 = l_Lean_mkAppN(x_192, x_191);
if (lean_is_scalar(x_177)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_177;
}
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_201 = lean_ctor_get(x_183, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_203 = x_183;
} else {
 lean_dec_ref(x_183);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_206 = l_Lean_Meta_mkEqRefl(x_205, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_211 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_212 = lean_array_push(x_211, x_1);
x_213 = lean_array_push(x_212, x_210);
x_214 = lean_array_push(x_213, x_207);
x_215 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_216 = l_Lean_mkAppN(x_215, x_214);
if (lean_is_scalar(x_177)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_177;
}
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_209)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_209;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_208);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_224 = lean_ctor_get(x_206, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
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
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_178, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_178, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_230 = x_178;
} else {
 lean_dec_ref(x_178);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_169, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_169, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_234 = x_169;
} else {
 lean_dec_ref(x_169);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_13);
if (x_236 == 0)
{
return x_13;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_13, 0);
x_238 = lean_ctor_get(x_13, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_13);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceGT___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceGT___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceGT___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGT), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9;
x_4 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_958_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Nat_fromExpr_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Nat_fromExpr_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_36 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_nat_dec_le(x_35, x_23);
lean_dec(x_23);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_41 = l_Lean_Meta_mkEqRefl(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_45 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_46 = lean_array_push(x_45, x_1);
x_47 = lean_array_push(x_46, x_44);
x_48 = lean_array_push(x_47, x_43);
x_49 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_50 = l_Lean_mkAppN(x_49, x_48);
lean_ctor_set(x_26, 0, x_50);
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_14, 0, x_54);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_58 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_57);
x_61 = lean_array_push(x_60, x_55);
x_62 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_63 = l_Lean_mkAppN(x_62, x_61);
lean_ctor_set(x_26, 0, x_63);
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_26);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_14, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_41);
if (x_69 == 0)
{
return x_41;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 0);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_41);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_74 = l_Lean_Meta_mkEqRefl(x_73, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_78 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_79 = lean_array_push(x_78, x_1);
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_array_push(x_80, x_76);
x_82 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_83 = l_Lean_mkAppN(x_82, x_81);
lean_ctor_set(x_26, 0, x_83);
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_26);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_14, 0, x_87);
lean_ctor_set(x_74, 0, x_14);
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_91 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_array_push(x_93, x_88);
x_95 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_96 = l_Lean_mkAppN(x_95, x_94);
lean_ctor_set(x_26, 0, x_96);
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_26);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_14, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_14);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_37);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_74);
if (x_102 == 0)
{
return x_74;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_74, 0);
x_104 = lean_ctor_get(x_74, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_74);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_26);
lean_dec(x_35);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
return x_36;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_36, 0);
x_108 = lean_ctor_get(x_36, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_36);
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
x_110 = lean_ctor_get(x_26, 0);
lean_inc(x_110);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_111 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_nat_dec_le(x_110, x_23);
lean_dec(x_23);
lean_dec(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_116 = l_Lean_Meta_mkEqRefl(x_115, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_121 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_120);
x_124 = lean_array_push(x_123, x_117);
x_125 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_126 = l_Lean_mkAppN(x_125, x_124);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_14, 0, x_131);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_119;
}
lean_ctor_set(x_132, 0, x_14);
lean_ctor_set(x_132, 1, x_118);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Expr_appArg_x21(x_112);
lean_dec(x_112);
x_143 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_144 = lean_array_push(x_143, x_1);
x_145 = lean_array_push(x_144, x_142);
x_146 = lean_array_push(x_145, x_139);
x_147 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_148 = l_Lean_mkAppN(x_147, x_146);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_14, 0, x_153);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_14);
lean_ctor_set(x_154, 1, x_140);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_112);
lean_free_object(x_14);
lean_dec(x_1);
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_157 = x_138;
} else {
 lean_dec_ref(x_138);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_110);
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_111, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_111, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_161 = x_111;
} else {
 lean_dec_ref(x_111);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_14);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_25);
if (x_163 == 0)
{
return x_25;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_25, 0);
x_165 = lean_ctor_get(x_25, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_25);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_14, 0);
lean_inc(x_167);
lean_dec(x_14);
x_168 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_169 = l_Nat_fromExpr_x3f(x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_178 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_nat_dec_le(x_176, x_167);
lean_dec(x_167);
lean_dec(x_176);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_183 = l_Lean_Meta_mkEqRefl(x_182, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_188 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_189 = lean_array_push(x_188, x_1);
x_190 = lean_array_push(x_189, x_187);
x_191 = lean_array_push(x_190, x_184);
x_192 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_193 = l_Lean_mkAppN(x_192, x_191);
if (lean_is_scalar(x_177)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_177;
}
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_201 = lean_ctor_get(x_183, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_203 = x_183;
} else {
 lean_dec_ref(x_183);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_206 = l_Lean_Meta_mkEqRefl(x_205, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Expr_appArg_x21(x_179);
lean_dec(x_179);
x_211 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_212 = lean_array_push(x_211, x_1);
x_213 = lean_array_push(x_212, x_210);
x_214 = lean_array_push(x_213, x_207);
x_215 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_216 = l_Lean_mkAppN(x_215, x_214);
if (lean_is_scalar(x_177)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_177;
}
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_209)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_209;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_208);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_1);
x_224 = lean_ctor_get(x_206, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
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
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_178, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_178, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_230 = x_178;
} else {
 lean_dec_ref(x_178);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_169, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_169, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_234 = x_169;
} else {
 lean_dec_ref(x_169);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_13);
if (x_236 == 0)
{
return x_13;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_13, 0);
x_238 = lean_ctor_get(x_13, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_13);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceGE___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceGE___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceGE___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGE), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8;
x_4 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_997_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2;
x_3 = 1;
x_4 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3;
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
l_Nat_reduceBinPred___lambda__1___closed__1 = _init_l_Nat_reduceBinPred___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__1);
l_Nat_reduceBinPred___lambda__1___closed__2 = _init_l_Nat_reduceBinPred___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__2);
l_Nat_reduceBinPred___lambda__1___closed__3 = _init_l_Nat_reduceBinPred___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__3);
l_Nat_reduceBinPred___lambda__1___closed__4 = _init_l_Nat_reduceBinPred___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__4);
l_Nat_reduceBinPred___lambda__1___closed__5 = _init_l_Nat_reduceBinPred___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__5);
l_Nat_reduceBinPred___lambda__1___closed__6 = _init_l_Nat_reduceBinPred___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__6);
l_Nat_reduceBinPred___lambda__1___closed__7 = _init_l_Nat_reduceBinPred___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__7);
l_Nat_reduceBinPred___lambda__1___closed__8 = _init_l_Nat_reduceBinPred___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__8);
l_Nat_reduceBinPred___lambda__1___closed__9 = _init_l_Nat_reduceBinPred___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__9);
l_Nat_reduceBinPred___lambda__1___closed__10 = _init_l_Nat_reduceBinPred___lambda__1___closed__10();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__10);
l_Nat_reduceBinPred___lambda__1___closed__11 = _init_l_Nat_reduceBinPred___lambda__1___closed__11();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__11);
l_Nat_reduceBinPred___lambda__1___closed__12 = _init_l_Nat_reduceBinPred___lambda__1___closed__12();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__12);
l_Nat_reduceBinPred___lambda__1___closed__13 = _init_l_Nat_reduceBinPred___lambda__1___closed__13();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__13);
l_Nat_reduceBinPred___lambda__1___closed__14 = _init_l_Nat_reduceBinPred___lambda__1___closed__14();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__14);
l_Nat_reduceBinPred___lambda__1___closed__15 = _init_l_Nat_reduceBinPred___lambda__1___closed__15();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__15);
l_Nat_reduceBinPred___lambda__1___closed__16 = _init_l_Nat_reduceBinPred___lambda__1___closed__16();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__16);
l_Nat_reduceBinPred___lambda__1___closed__17 = _init_l_Nat_reduceBinPred___lambda__1___closed__17();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__17);
l_Nat_reduceBinPred___lambda__1___closed__18 = _init_l_Nat_reduceBinPred___lambda__1___closed__18();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__18);
l_Nat_reduceBinPred___lambda__1___closed__19 = _init_l_Nat_reduceBinPred___lambda__1___closed__19();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__19);
l_Nat_reduceBinPred___lambda__1___closed__20 = _init_l_Nat_reduceBinPred___lambda__1___closed__20();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__20);
l_Nat_reduceSucc___closed__1 = _init_l_Nat_reduceSucc___closed__1();
lean_mark_persistent(l_Nat_reduceSucc___closed__1);
l_Nat_reduceSucc___closed__2 = _init_l_Nat_reduceSucc___closed__2();
lean_mark_persistent(l_Nat_reduceSucc___closed__2);
l_Nat_reduceSucc___closed__3 = _init_l_Nat_reduceSucc___closed__3();
lean_mark_persistent(l_Nat_reduceSucc___closed__3);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__1);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__2);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__3);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__4);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__5);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__6);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_592_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_594_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceAdd___closed__1 = _init_l_Nat_reduceAdd___closed__1();
lean_mark_persistent(l_Nat_reduceAdd___closed__1);
l_Nat_reduceAdd___closed__2 = _init_l_Nat_reduceAdd___closed__2();
lean_mark_persistent(l_Nat_reduceAdd___closed__2);
l_Nat_reduceAdd___closed__3 = _init_l_Nat_reduceAdd___closed__3();
lean_mark_persistent(l_Nat_reduceAdd___closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__1);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__2);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__4);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__5);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__6);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__7);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__8);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__9);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__10);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__11);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__12);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__13);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630____closed__14);
if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_630_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_632_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMul___closed__1 = _init_l_Nat_reduceMul___closed__1();
lean_mark_persistent(l_Nat_reduceMul___closed__1);
l_Nat_reduceMul___closed__2 = _init_l_Nat_reduceMul___closed__2();
lean_mark_persistent(l_Nat_reduceMul___closed__2);
l_Nat_reduceMul___closed__3 = _init_l_Nat_reduceMul___closed__3();
lean_mark_persistent(l_Nat_reduceMul___closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__1);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__2);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__4);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__5);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__6);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__7);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__8);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__9);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__10);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_668_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_670_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceSub___closed__1 = _init_l_Nat_reduceSub___closed__1();
lean_mark_persistent(l_Nat_reduceSub___closed__1);
l_Nat_reduceSub___closed__2 = _init_l_Nat_reduceSub___closed__2();
lean_mark_persistent(l_Nat_reduceSub___closed__2);
l_Nat_reduceSub___closed__3 = _init_l_Nat_reduceSub___closed__3();
lean_mark_persistent(l_Nat_reduceSub___closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__1);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__2);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__4);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__5);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__6);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__7);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__8);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__9);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__10);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_706_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_708_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceDiv___closed__1 = _init_l_Nat_reduceDiv___closed__1();
lean_mark_persistent(l_Nat_reduceDiv___closed__1);
l_Nat_reduceDiv___closed__2 = _init_l_Nat_reduceDiv___closed__2();
lean_mark_persistent(l_Nat_reduceDiv___closed__2);
l_Nat_reduceDiv___closed__3 = _init_l_Nat_reduceDiv___closed__3();
lean_mark_persistent(l_Nat_reduceDiv___closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__1);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__2);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__4);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__5);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__6);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__7);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__8);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__9);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__10);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_744_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_746_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMod___closed__1 = _init_l_Nat_reduceMod___closed__1();
lean_mark_persistent(l_Nat_reduceMod___closed__1);
l_Nat_reduceMod___closed__2 = _init_l_Nat_reduceMod___closed__2();
lean_mark_persistent(l_Nat_reduceMod___closed__2);
l_Nat_reduceMod___closed__3 = _init_l_Nat_reduceMod___closed__3();
lean_mark_persistent(l_Nat_reduceMod___closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__1);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__2);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__4);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__5);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__6);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__7);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__8);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__9);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__10);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_782_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_784_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reducePow___closed__1 = _init_l_Nat_reducePow___closed__1();
lean_mark_persistent(l_Nat_reducePow___closed__1);
l_Nat_reducePow___closed__2 = _init_l_Nat_reducePow___closed__2();
lean_mark_persistent(l_Nat_reducePow___closed__2);
l_Nat_reducePow___closed__3 = _init_l_Nat_reducePow___closed__3();
lean_mark_persistent(l_Nat_reducePow___closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__1);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__2);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__4);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__5);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__6);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__7);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__8);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__9);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__10);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_820_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_822_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGcd___closed__1 = _init_l_Nat_reduceGcd___closed__1();
lean_mark_persistent(l_Nat_reduceGcd___closed__1);
l_Nat_reduceGcd___closed__2 = _init_l_Nat_reduceGcd___closed__2();
lean_mark_persistent(l_Nat_reduceGcd___closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__1);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__3);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__4);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__5);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__6);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_839_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_841_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLT___closed__1 = _init_l_Nat_reduceLT___closed__1();
lean_mark_persistent(l_Nat_reduceLT___closed__1);
l_Nat_reduceLT___closed__2 = _init_l_Nat_reduceLT___closed__2();
lean_mark_persistent(l_Nat_reduceLT___closed__2);
l_Nat_reduceLT___closed__3 = _init_l_Nat_reduceLT___closed__3();
lean_mark_persistent(l_Nat_reduceLT___closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__1);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__2);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__4);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__5);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__6);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__7);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__8);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__9);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878____closed__10);
if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_878_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_880_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLE___closed__1 = _init_l_Nat_reduceLE___closed__1();
lean_mark_persistent(l_Nat_reduceLE___closed__1);
l_Nat_reduceLE___closed__2 = _init_l_Nat_reduceLE___closed__2();
lean_mark_persistent(l_Nat_reduceLE___closed__2);
l_Nat_reduceLE___closed__3 = _init_l_Nat_reduceLE___closed__3();
lean_mark_persistent(l_Nat_reduceLE___closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__1);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__2);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__4);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__5);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__6);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__7);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__8);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917____closed__9);
if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_917_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_919_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGT___closed__1 = _init_l_Nat_reduceGT___closed__1();
lean_mark_persistent(l_Nat_reduceGT___closed__1);
l_Nat_reduceGT___closed__2 = _init_l_Nat_reduceGT___closed__2();
lean_mark_persistent(l_Nat_reduceGT___closed__2);
l_Nat_reduceGT___closed__3 = _init_l_Nat_reduceGT___closed__3();
lean_mark_persistent(l_Nat_reduceGT___closed__3);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__1);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__2);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_956_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_958_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGE___closed__1 = _init_l_Nat_reduceGE___closed__1();
lean_mark_persistent(l_Nat_reduceGE___closed__1);
l_Nat_reduceGE___closed__2 = _init_l_Nat_reduceGE___closed__2();
lean_mark_persistent(l_Nat_reduceGE___closed__2);
l_Nat_reduceGE___closed__3 = _init_l_Nat_reduceGE___closed__3();
lean_mark_persistent(l_Nat_reduceGE___closed__3);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__1);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__2);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_995_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_997_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
