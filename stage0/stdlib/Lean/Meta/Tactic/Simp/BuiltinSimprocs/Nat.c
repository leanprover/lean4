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
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973_(lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSub___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_897_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11;
static lean_object* l_Nat_reduceSub___closed__1;
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7;
static lean_object* l_Nat_reduceDiv___closed__3;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9;
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9;
static lean_object* l_Nat_reduceMod___closed__2;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8;
static lean_object* l_Nat_reduceDiv___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760_(lean_object*);
static lean_object* l_Nat_reduceMul___closed__2;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2;
static lean_object* l_Nat_reduceDiv___closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3;
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646_(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__2;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_686_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__16;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_975_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7;
static lean_object* l_Nat_isValue___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7;
static lean_object* l_Nat_reduceGE___closed__2;
static lean_object* l_Nat_reduceGcd___closed__1;
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_819_(lean_object*);
extern lean_object* l_Lean_Meta_Simp_builtinSimprocsRef;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceLE___closed__1;
static lean_object* l_Nat_reduceSub___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2;
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_936_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4;
static lean_object* l_Nat_reduceGT___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Nat_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1;
static lean_object* l_Nat_reduceGT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1;
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceLT___closed__3;
static lean_object* l_Nat_reduceLT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7;
static lean_object* l_Nat_reduceLE___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Nat_reduceMod___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817_(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__20;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__14;
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6;
static lean_object* l_Nat_reduceAdd___closed__2;
static lean_object* l_Nat_reduceGE___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_610_(lean_object*);
static lean_object* l_Nat_reduceSucc___closed__2;
static lean_object* l_Nat_reduceUnary___lambda__1___closed__1;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_648_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__1;
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceMul___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__15;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__10;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_762_(lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceGE___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLE___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__19;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGcd___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_724_(lean_object*);
static lean_object* l_Nat_reduceGT___closed__2;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3;
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6;
static lean_object* l_Nat_reduceMod___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856_(lean_object*);
static lean_object* l_Nat_reduceSucc___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1104_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_858_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8;
static lean_object* l_Nat_reduceMul___closed__3;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6;
static lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1;
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGE___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_isValue___lambda__2___closed__2;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5;
static lean_object* l_Nat_isValue___lambda__2___closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11;
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_800_(lean_object*);
static lean_object* l_Nat_reduceLE___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6;
static lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceLT___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
static lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6;
static lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5;
static lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__18;
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608_(lean_object*);
static lean_object* l_Nat_reduceSucc___closed__1;
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__11;
static lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5;
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Nat_reduceUnary___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_apply_1(x_2, x_23);
x_25 = l_Lean_mkNatLit(x_24);
x_26 = lean_box(0);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_apply_1(x_2, x_31);
x_33 = l_Lean_mkNatLit(x_32);
x_34 = lean_box(0);
x_35 = 0;
x_36 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set_uint32(x_36, sizeof(void*)*2, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_14 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_18 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_29 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_apply_2(x_2, x_23, x_35);
x_37 = l_Lean_mkNatLit(x_36);
x_38 = lean_box(0);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint32(x_40, sizeof(void*)*2, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint32_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_apply_2(x_2, x_23, x_43);
x_45 = l_Lean_mkNatLit(x_44);
x_46 = lean_box(0);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_25);
if (x_51 == 0)
{
return x_25;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_25, 0);
x_53 = lean_ctor_get(x_25, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_25);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
x_14 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_18 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = l_Lean_Meta_mkDecide(x_1, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_2(x_2, x_23, x_35);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_42 = l_Lean_Meta_mkEqRefl(x_41, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_46 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_47 = lean_array_push(x_46, x_1);
x_48 = lean_array_push(x_47, x_45);
x_49 = lean_array_push(x_48, x_44);
x_50 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_51 = l_Lean_mkAppN(x_50, x_49);
lean_ctor_set(x_26, 0, x_51);
x_52 = 0;
x_53 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_54 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_26);
lean_ctor_set_uint32(x_54, sizeof(void*)*2, x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_42, 0, x_55);
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint32_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_59 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_60 = lean_array_push(x_59, x_1);
x_61 = lean_array_push(x_60, x_58);
x_62 = lean_array_push(x_61, x_56);
x_63 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_64 = l_Lean_mkAppN(x_63, x_62);
lean_ctor_set(x_26, 0, x_64);
x_65 = 0;
x_66 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_67 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_26);
lean_ctor_set_uint32(x_67, sizeof(void*)*2, x_65);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_42);
if (x_70 == 0)
{
return x_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_42, 0);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_42);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_75 = l_Lean_Meta_mkEqRefl(x_74, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint32_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_79 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_80 = lean_array_push(x_79, x_1);
x_81 = lean_array_push(x_80, x_78);
x_82 = lean_array_push(x_81, x_77);
x_83 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_84 = l_Lean_mkAppN(x_83, x_82);
lean_ctor_set(x_26, 0, x_84);
x_85 = 0;
x_86 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_87 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_26);
lean_ctor_set_uint32(x_87, sizeof(void*)*2, x_85);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_75, 0, x_88);
return x_75;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
x_91 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_92 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_93 = lean_array_push(x_92, x_1);
x_94 = lean_array_push(x_93, x_91);
x_95 = lean_array_push(x_94, x_89);
x_96 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_97 = l_Lean_mkAppN(x_96, x_95);
lean_ctor_set(x_26, 0, x_97);
x_98 = 0;
x_99 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_100 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_26);
lean_ctor_set_uint32(x_100, sizeof(void*)*2, x_98);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_37);
lean_free_object(x_26);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_75);
if (x_103 == 0)
{
return x_75;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_75, 0);
x_105 = lean_ctor_get(x_75, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_75);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_free_object(x_26);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_36);
if (x_107 == 0)
{
return x_36;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_36, 0);
x_109 = lean_ctor_get(x_36, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_36);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_26, 0);
lean_inc(x_111);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_112 = l_Lean_Meta_mkDecide(x_1, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_apply_2(x_2, x_23, x_111);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_118 = l_Lean_Meta_mkEqRefl(x_117, x_7, x_8, x_9, x_10, x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint32_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l_Lean_Expr_appArg_x21(x_113);
lean_dec(x_113);
x_123 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_124 = lean_array_push(x_123, x_1);
x_125 = lean_array_push(x_124, x_122);
x_126 = lean_array_push(x_125, x_119);
x_127 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_128 = l_Lean_mkAppN(x_127, x_126);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = 0;
x_131 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_132 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set_uint32(x_132, sizeof(void*)*2, x_130);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_121)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_121;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_113);
lean_dec(x_1);
x_135 = lean_ctor_get(x_118, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_137 = x_118;
} else {
 lean_dec_ref(x_118);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_140 = l_Lean_Meta_mkEqRefl(x_139, x_7, x_8, x_9, x_10, x_114);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint32_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = l_Lean_Expr_appArg_x21(x_113);
lean_dec(x_113);
x_145 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_146 = lean_array_push(x_145, x_1);
x_147 = lean_array_push(x_146, x_144);
x_148 = lean_array_push(x_147, x_141);
x_149 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_150 = l_Lean_mkAppN(x_149, x_148);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = 0;
x_153 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_154 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
lean_ctor_set_uint32(x_154, sizeof(void*)*2, x_152);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_143)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_143;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_142);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_113);
lean_dec(x_1);
x_157 = lean_ctor_get(x_140, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_140, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_159 = x_140;
} else {
 lean_dec_ref(x_140);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_111);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_112, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_112, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_163 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
else
{
uint8_t x_165; 
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_25);
if (x_165 == 0)
{
return x_25;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_25, 0);
x_167 = lean_ctor_get(x_25, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_25);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_14);
if (x_169 == 0)
{
return x_14;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_14, 0);
x_171 = lean_ctor_get(x_14, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_14);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
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
x_14 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_16 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_mkNatLit(x_24);
x_26 = lean_box(0);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint32(x_37, sizeof(void*)*2, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
}
else
{
uint8_t x_40; 
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSucc", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4;
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2;
x_3 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6;
x_4 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSimprocsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_add(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_add(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceAdd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceSucc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2;
x_3 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13;
x_4 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_610_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_mul(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_mul(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMul", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2;
x_3 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10;
x_4 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_648_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_sub(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_sub(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceSub", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10;
x_4 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_686_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_div(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_div(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceDiv", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2;
x_3 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10;
x_4 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_724_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_mod(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_mod(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceMod", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2;
x_3 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10;
x_4 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_762_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_pow(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_pow(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reducePow", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6;
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2;
x_3 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10;
x_4 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_800_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_gcd(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
x_36 = l_Lean_mkNatLit(x_35);
x_37 = lean_box(0);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint32(x_39, sizeof(void*)*2, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_nat_gcd(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_44 = l_Lean_mkNatLit(x_43);
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint32(x_47, sizeof(void*)*2, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGcd", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2;
x_3 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6;
x_4 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_819_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_dec_lt(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_40 = l_Lean_Meta_mkEqRefl(x_39, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_44 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_array_push(x_46, x_42);
x_48 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_49 = l_Lean_mkAppN(x_48, x_47);
lean_ctor_set(x_25, 0, x_49);
x_50 = 0;
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set_uint32(x_52, sizeof(void*)*2, x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_57 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_54);
x_61 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_62 = l_Lean_mkAppN(x_61, x_60);
lean_ctor_set(x_25, 0, x_62);
x_63 = 0;
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set_uint32(x_65, sizeof(void*)*2, x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_73 = l_Lean_Meta_mkEqRefl(x_72, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_77 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_76);
x_80 = lean_array_push(x_79, x_75);
x_81 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_82 = l_Lean_mkAppN(x_81, x_80);
lean_ctor_set(x_25, 0, x_82);
x_83 = 0;
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_25);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_90 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_91 = lean_array_push(x_90, x_1);
x_92 = lean_array_push(x_91, x_89);
x_93 = lean_array_push(x_92, x_87);
x_94 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_ctor_set(x_25, 0, x_95);
x_96 = 0;
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_25);
lean_ctor_set_uint32(x_98, sizeof(void*)*2, x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_73);
if (x_101 == 0)
{
return x_73;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_25);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_25, 0);
lean_inc(x_109);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_110 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_nat_dec_lt(x_22, x_109);
lean_dec(x_109);
lean_dec(x_22);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_115 = l_Lean_Meta_mkEqRefl(x_114, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_120 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_121 = lean_array_push(x_120, x_1);
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_116);
x_124 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_125 = l_Lean_mkAppN(x_124, x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = 0;
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set_uint32(x_129, sizeof(void*)*2, x_127);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_117);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_1);
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_137 = l_Lean_Meta_mkEqRefl(x_136, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint32_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_142 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_array_push(x_143, x_141);
x_145 = lean_array_push(x_144, x_138);
x_146 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_147 = l_Lean_mkAppN(x_146, x_145);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = 0;
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set_uint32(x_151, sizeof(void*)*2, x_149);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_140)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_140;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_139);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
lean_dec(x_1);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_137, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_156 = x_137;
} else {
 lean_dec_ref(x_137);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_109);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_ctor_get(x_110, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_110, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_160 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
uint8_t x_162; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_24);
if (x_162 == 0)
{
return x_24;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_24, 0);
x_164 = lean_ctor_get(x_24, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_24);
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
uint8_t x_166; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_13);
if (x_166 == 0)
{
return x_13;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_13, 0);
x_168 = lean_ctor_get(x_13, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_13);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4;
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLT), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9;
x_4 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_858_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_dec_le(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_40 = l_Lean_Meta_mkEqRefl(x_39, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_44 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_array_push(x_46, x_42);
x_48 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_49 = l_Lean_mkAppN(x_48, x_47);
lean_ctor_set(x_25, 0, x_49);
x_50 = 0;
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set_uint32(x_52, sizeof(void*)*2, x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_57 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_54);
x_61 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_62 = l_Lean_mkAppN(x_61, x_60);
lean_ctor_set(x_25, 0, x_62);
x_63 = 0;
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set_uint32(x_65, sizeof(void*)*2, x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_73 = l_Lean_Meta_mkEqRefl(x_72, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_77 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_76);
x_80 = lean_array_push(x_79, x_75);
x_81 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_82 = l_Lean_mkAppN(x_81, x_80);
lean_ctor_set(x_25, 0, x_82);
x_83 = 0;
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_25);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_90 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_91 = lean_array_push(x_90, x_1);
x_92 = lean_array_push(x_91, x_89);
x_93 = lean_array_push(x_92, x_87);
x_94 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_ctor_set(x_25, 0, x_95);
x_96 = 0;
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_25);
lean_ctor_set_uint32(x_98, sizeof(void*)*2, x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_73);
if (x_101 == 0)
{
return x_73;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_25);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_25, 0);
lean_inc(x_109);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_110 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_nat_dec_le(x_22, x_109);
lean_dec(x_109);
lean_dec(x_22);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_115 = l_Lean_Meta_mkEqRefl(x_114, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_120 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_121 = lean_array_push(x_120, x_1);
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_116);
x_124 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_125 = l_Lean_mkAppN(x_124, x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = 0;
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set_uint32(x_129, sizeof(void*)*2, x_127);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_117);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_1);
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_137 = l_Lean_Meta_mkEqRefl(x_136, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint32_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_142 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_array_push(x_143, x_141);
x_145 = lean_array_push(x_144, x_138);
x_146 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_147 = l_Lean_mkAppN(x_146, x_145);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = 0;
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set_uint32(x_151, sizeof(void*)*2, x_149);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_140)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_140;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_139);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
lean_dec(x_1);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_137, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_156 = x_137;
} else {
 lean_dec_ref(x_137);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_109);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_ctor_get(x_110, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_110, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_160 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
uint8_t x_162; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_24);
if (x_162 == 0)
{
return x_24;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_24, 0);
x_164 = lean_ctor_get(x_24, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_24);
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
uint8_t x_166; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_13);
if (x_166 == 0)
{
return x_13;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_13, 0);
x_168 = lean_ctor_get(x_13, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_13);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceLE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4;
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLE), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8;
x_4 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_897_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_dec_lt(x_34, x_22);
lean_dec(x_22);
lean_dec(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_40 = l_Lean_Meta_mkEqRefl(x_39, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_44 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_array_push(x_46, x_42);
x_48 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_49 = l_Lean_mkAppN(x_48, x_47);
lean_ctor_set(x_25, 0, x_49);
x_50 = 0;
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set_uint32(x_52, sizeof(void*)*2, x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_57 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_54);
x_61 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_62 = l_Lean_mkAppN(x_61, x_60);
lean_ctor_set(x_25, 0, x_62);
x_63 = 0;
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set_uint32(x_65, sizeof(void*)*2, x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_73 = l_Lean_Meta_mkEqRefl(x_72, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_77 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_76);
x_80 = lean_array_push(x_79, x_75);
x_81 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_82 = l_Lean_mkAppN(x_81, x_80);
lean_ctor_set(x_25, 0, x_82);
x_83 = 0;
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_25);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_90 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_91 = lean_array_push(x_90, x_1);
x_92 = lean_array_push(x_91, x_89);
x_93 = lean_array_push(x_92, x_87);
x_94 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_ctor_set(x_25, 0, x_95);
x_96 = 0;
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_25);
lean_ctor_set_uint32(x_98, sizeof(void*)*2, x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_73);
if (x_101 == 0)
{
return x_73;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_25);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_25, 0);
lean_inc(x_109);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_110 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_nat_dec_lt(x_109, x_22);
lean_dec(x_22);
lean_dec(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_115 = l_Lean_Meta_mkEqRefl(x_114, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_120 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_121 = lean_array_push(x_120, x_1);
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_116);
x_124 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_125 = l_Lean_mkAppN(x_124, x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = 0;
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set_uint32(x_129, sizeof(void*)*2, x_127);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_117);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_1);
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_137 = l_Lean_Meta_mkEqRefl(x_136, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint32_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_142 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_array_push(x_143, x_141);
x_145 = lean_array_push(x_144, x_138);
x_146 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_147 = l_Lean_mkAppN(x_146, x_145);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = 0;
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set_uint32(x_151, sizeof(void*)*2, x_149);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_140)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_140;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_139);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
lean_dec(x_1);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_137, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_156 = x_137;
} else {
 lean_dec_ref(x_137);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_109);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_ctor_get(x_110, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_110, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_160 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
uint8_t x_162; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_24);
if (x_162 == 0)
{
return x_24;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_24, 0);
x_164 = lean_ctor_get(x_24, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_24);
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
uint8_t x_166; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_13);
if (x_166 == 0)
{
return x_13;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_13, 0);
x_168 = lean_ctor_get(x_13, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_13);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGT", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGT), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9;
x_4 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_936_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceUnary___lambda__1___closed__1;
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceUnary___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_dec_le(x_34, x_22);
lean_dec(x_22);
lean_dec(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_40 = l_Lean_Meta_mkEqRefl(x_39, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_44 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_array_push(x_46, x_42);
x_48 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_49 = l_Lean_mkAppN(x_48, x_47);
lean_ctor_set(x_25, 0, x_49);
x_50 = 0;
x_51 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_52 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set_uint32(x_52, sizeof(void*)*2, x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_57 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_54);
x_61 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_62 = l_Lean_mkAppN(x_61, x_60);
lean_ctor_set(x_25, 0, x_62);
x_63 = 0;
x_64 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_65 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set_uint32(x_65, sizeof(void*)*2, x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_73 = l_Lean_Meta_mkEqRefl(x_72, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_77 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_76);
x_80 = lean_array_push(x_79, x_75);
x_81 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_82 = l_Lean_mkAppN(x_81, x_80);
lean_ctor_set(x_25, 0, x_82);
x_83 = 0;
x_84 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_85 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_25);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_83);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_90 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_91 = lean_array_push(x_90, x_1);
x_92 = lean_array_push(x_91, x_89);
x_93 = lean_array_push(x_92, x_87);
x_94 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_ctor_set(x_25, 0, x_95);
x_96 = 0;
x_97 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_98 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_25);
lean_ctor_set_uint32(x_98, sizeof(void*)*2, x_96);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_73);
if (x_101 == 0)
{
return x_73;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_25);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_25, 0);
lean_inc(x_109);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_110 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_nat_dec_le(x_109, x_22);
lean_dec(x_22);
lean_dec(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Nat_reduceBinPred___lambda__1___closed__4;
x_115 = l_Lean_Meta_mkEqRefl(x_114, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_120 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_121 = lean_array_push(x_120, x_1);
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_116);
x_124 = l_Nat_reduceBinPred___lambda__1___closed__10;
x_125 = l_Lean_mkAppN(x_124, x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = 0;
x_128 = l_Nat_reduceBinPred___lambda__1___closed__7;
x_129 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set_uint32(x_129, sizeof(void*)*2, x_127);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_117);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_1);
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Nat_reduceBinPred___lambda__1___closed__14;
x_137 = l_Lean_Meta_mkEqRefl(x_136, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint32_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_142 = l_Nat_reduceBinPred___lambda__1___closed__11;
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_array_push(x_143, x_141);
x_145 = lean_array_push(x_144, x_138);
x_146 = l_Nat_reduceBinPred___lambda__1___closed__20;
x_147 = l_Lean_mkAppN(x_146, x_145);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = 0;
x_150 = l_Nat_reduceBinPred___lambda__1___closed__17;
x_151 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set_uint32(x_151, sizeof(void*)*2, x_149);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_140)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_140;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_139);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
lean_dec(x_1);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_137, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_156 = x_137;
} else {
 lean_dec_ref(x_137);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_109);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_ctor_get(x_110, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_110, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_160 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
uint8_t x_162; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_24);
if (x_162 == 0)
{
return x_24;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_24, 0);
x_164 = lean_ctor_get(x_24, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_24);
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
uint8_t x_166; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_13);
if (x_166 == 0)
{
return x_13;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_13, 0);
x_168 = lean_ctor_get(x_13, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_13);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_13 = l_Nat_reduceUnary___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceGE", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGE), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2;
x_3 = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8;
x_4 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_975_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
static lean_object* _init_l_Nat_isValue___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_isValue___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Nat_isValue___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_isValue___lambda__2___closed__1;
x_2 = l_Nat_isValue___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_2);
x_11 = l_Nat_isValue___lambda__2___closed__3;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Nat_reduceUnary___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Nat_isValue___lambda__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Nat_reduceUnary___lambda__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Nat_isValue___lambda__2(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_isValue___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_isValue___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isValue", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_isValue___lambda__2___closed__3;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4;
x_2 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7;
x_2 = lean_box(3);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_isValue), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2;
x_3 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8;
x_4 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1104_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1;
x_3 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
l_Nat_reduceUnary___lambda__1___closed__1 = _init_l_Nat_reduceUnary___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceUnary___lambda__1___closed__1);
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
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__1);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__2);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__3);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__4);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__5);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__6);
l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_570_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_572_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceAdd___closed__1 = _init_l_Nat_reduceAdd___closed__1();
lean_mark_persistent(l_Nat_reduceAdd___closed__1);
l_Nat_reduceAdd___closed__2 = _init_l_Nat_reduceAdd___closed__2();
lean_mark_persistent(l_Nat_reduceAdd___closed__2);
l_Nat_reduceAdd___closed__3 = _init_l_Nat_reduceAdd___closed__3();
lean_mark_persistent(l_Nat_reduceAdd___closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__1);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__2);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__3);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__4);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__5);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__6);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__7);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__8);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__9);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__10);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__11);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__12);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__13);
l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14 = _init_l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608____closed__14);
if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_608_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_610_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMul___closed__1 = _init_l_Nat_reduceMul___closed__1();
lean_mark_persistent(l_Nat_reduceMul___closed__1);
l_Nat_reduceMul___closed__2 = _init_l_Nat_reduceMul___closed__2();
lean_mark_persistent(l_Nat_reduceMul___closed__2);
l_Nat_reduceMul___closed__3 = _init_l_Nat_reduceMul___closed__3();
lean_mark_persistent(l_Nat_reduceMul___closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__1);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__2);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__3);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__4);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__5);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__6);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__7);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__8);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__9);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__10);
l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11 = _init_l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_646_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_648_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceSub___closed__1 = _init_l_Nat_reduceSub___closed__1();
lean_mark_persistent(l_Nat_reduceSub___closed__1);
l_Nat_reduceSub___closed__2 = _init_l_Nat_reduceSub___closed__2();
lean_mark_persistent(l_Nat_reduceSub___closed__2);
l_Nat_reduceSub___closed__3 = _init_l_Nat_reduceSub___closed__3();
lean_mark_persistent(l_Nat_reduceSub___closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__1);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__2);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__3);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__4);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__5);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__6);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__7);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__8);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__9);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__10);
l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11 = _init_l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_684_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_686_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceDiv___closed__1 = _init_l_Nat_reduceDiv___closed__1();
lean_mark_persistent(l_Nat_reduceDiv___closed__1);
l_Nat_reduceDiv___closed__2 = _init_l_Nat_reduceDiv___closed__2();
lean_mark_persistent(l_Nat_reduceDiv___closed__2);
l_Nat_reduceDiv___closed__3 = _init_l_Nat_reduceDiv___closed__3();
lean_mark_persistent(l_Nat_reduceDiv___closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__1);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__2);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__3);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__4);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__5);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__6);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__7);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__8);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__9);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__10);
l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11 = _init_l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_722_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_724_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMod___closed__1 = _init_l_Nat_reduceMod___closed__1();
lean_mark_persistent(l_Nat_reduceMod___closed__1);
l_Nat_reduceMod___closed__2 = _init_l_Nat_reduceMod___closed__2();
lean_mark_persistent(l_Nat_reduceMod___closed__2);
l_Nat_reduceMod___closed__3 = _init_l_Nat_reduceMod___closed__3();
lean_mark_persistent(l_Nat_reduceMod___closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__1);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__2);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__3);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__4);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__5);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__6);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__7);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__8);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__9);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__10);
l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11 = _init_l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_760_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_762_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reducePow___closed__1 = _init_l_Nat_reducePow___closed__1();
lean_mark_persistent(l_Nat_reducePow___closed__1);
l_Nat_reducePow___closed__2 = _init_l_Nat_reducePow___closed__2();
lean_mark_persistent(l_Nat_reducePow___closed__2);
l_Nat_reducePow___closed__3 = _init_l_Nat_reducePow___closed__3();
lean_mark_persistent(l_Nat_reducePow___closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__1);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__2);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__3);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__4);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__5);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__6);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__7);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__8);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__9);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__10);
l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11 = _init_l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798____closed__11);
if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_798_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_800_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGcd___closed__1 = _init_l_Nat_reduceGcd___closed__1();
lean_mark_persistent(l_Nat_reduceGcd___closed__1);
l_Nat_reduceGcd___closed__2 = _init_l_Nat_reduceGcd___closed__2();
lean_mark_persistent(l_Nat_reduceGcd___closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__1);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__2);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__3);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__4);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__5);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__6);
l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7 = _init_l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_817_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_819_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLT___closed__1 = _init_l_Nat_reduceLT___closed__1();
lean_mark_persistent(l_Nat_reduceLT___closed__1);
l_Nat_reduceLT___closed__2 = _init_l_Nat_reduceLT___closed__2();
lean_mark_persistent(l_Nat_reduceLT___closed__2);
l_Nat_reduceLT___closed__3 = _init_l_Nat_reduceLT___closed__3();
lean_mark_persistent(l_Nat_reduceLT___closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__1);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__2);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__3);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__4);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__5);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__6);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__7);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__8);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__9);
l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10 = _init_l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856____closed__10);
if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_856_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_858_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLE___closed__1 = _init_l_Nat_reduceLE___closed__1();
lean_mark_persistent(l_Nat_reduceLE___closed__1);
l_Nat_reduceLE___closed__2 = _init_l_Nat_reduceLE___closed__2();
lean_mark_persistent(l_Nat_reduceLE___closed__2);
l_Nat_reduceLE___closed__3 = _init_l_Nat_reduceLE___closed__3();
lean_mark_persistent(l_Nat_reduceLE___closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__1);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__2);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__3);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__4);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__5);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__6);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__7);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__8);
l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9 = _init_l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895____closed__9);
if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_895_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_897_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGT___closed__1 = _init_l_Nat_reduceGT___closed__1();
lean_mark_persistent(l_Nat_reduceGT___closed__1);
l_Nat_reduceGT___closed__2 = _init_l_Nat_reduceGT___closed__2();
lean_mark_persistent(l_Nat_reduceGT___closed__2);
l_Nat_reduceGT___closed__3 = _init_l_Nat_reduceGT___closed__3();
lean_mark_persistent(l_Nat_reduceGT___closed__3);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__1);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__2);
l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3 = _init_l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_934_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_936_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGE___closed__1 = _init_l_Nat_reduceGE___closed__1();
lean_mark_persistent(l_Nat_reduceGE___closed__1);
l_Nat_reduceGE___closed__2 = _init_l_Nat_reduceGE___closed__2();
lean_mark_persistent(l_Nat_reduceGE___closed__2);
l_Nat_reduceGE___closed__3 = _init_l_Nat_reduceGE___closed__3();
lean_mark_persistent(l_Nat_reduceGE___closed__3);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__1);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__2);
l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3 = _init_l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_973_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGE_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_975_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_isValue___lambda__2___closed__1 = _init_l_Nat_isValue___lambda__2___closed__1();
lean_mark_persistent(l_Nat_isValue___lambda__2___closed__1);
l_Nat_isValue___lambda__2___closed__2 = _init_l_Nat_isValue___lambda__2___closed__2();
lean_mark_persistent(l_Nat_isValue___lambda__2___closed__2);
l_Nat_isValue___lambda__2___closed__3 = _init_l_Nat_isValue___lambda__2___closed__3();
lean_mark_persistent(l_Nat_isValue___lambda__2___closed__3);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__1);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__2);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__3);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__4);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__5);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__6);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__7);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__8);
l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9 = _init_l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102____closed__9);
if (builtin) {res = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1102_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_isValue_declare____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1104_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
