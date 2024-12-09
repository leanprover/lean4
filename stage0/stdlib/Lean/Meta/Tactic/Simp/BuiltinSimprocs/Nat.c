// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: Init.Simproc Init.Data.Nat.Simproc Lean.Util.SafeExponentiation Lean.Meta.LitValues Lean.Meta.Offset Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
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
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__6;
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__5;
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__11;
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1;
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1;
static lean_object* l_Nat_reduceXor___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4;
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__8;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3;
static lean_object* l_Nat_reduceNatEqExpr___closed__13;
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6;
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1;
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2;
static lean_object* l_Nat_reduceSub___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4;
static lean_object* l_Nat_reduceNatEqExpr___closed__6;
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5;
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6;
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
static lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1;
static lean_object* l_Nat_reduceSub___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_object*);
static lean_object* l_Nat_reduceDiv___closed__3;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5;
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9;
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4;
extern lean_object* l_Lean_Nat_mkInstAdd;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4;
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6;
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceXor___closed__2;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__9;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__5;
static lean_object* l_Nat_reduceMod___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1;
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_object*);
static lean_object* l_Nat_reduceDiv___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1;
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3;
static lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceShiftLeft___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__2;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8;
static lean_object* l_Nat_reduceMul___closed__2;
static lean_object* l_Nat_reduceDiv___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__3;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9;
lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10;
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_object*);
static lean_object* l_Nat_reduceShiftLeft___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2;
static lean_object* l_Nat_reduceNatEqExpr___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1;
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__10;
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Nat_isValue___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_object*);
static lean_object* l_Nat_isValue___closed__1;
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceShiftRight___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__5;
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__7;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5;
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8;
static lean_object* l_Nat_reduceNatEqExpr___closed__10;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1;
static lean_object* l_Nat_reduceGcd___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_Simp_builtinSimprocsRef;
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1;
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_object*);
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__7;
static lean_object* l_Nat_reduceSub___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1;
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5;
static lean_object* l_Nat_reduceShiftRight___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_object*);
static lean_object* l_Nat_reduceNatEqExpr___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1;
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGT___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4;
static lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGT___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2;
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5;
static lean_object* l_Nat_reduceLT___closed__3;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__13;
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3;
static lean_object* l_Nat_reduceLT___closed__1;
static lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__8;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__10;
static lean_object* l_Nat_reduceNatEqExpr___closed__12;
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2;
static lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7;
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4;
static lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Nat_reduceMod___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4;
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__3;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__5;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBinPred___lambda__1___closed__1;
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8;
static lean_object* l_Nat_reduceNatEqExpr___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1;
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__1(lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6;
static lean_object* l_Nat_reduceAnd___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBEq___closed__3;
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__2;
static lean_object* l_Nat_reduceSucc___closed__2;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
static lean_object* l_Nat_reduceUnary___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceXor___closed__3;
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5;
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3;
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reducePow___closed__1;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__4;
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1;
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAnd___closed__1;
static lean_object* l_Nat_reduceNatEqExpr___closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__1;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_object*);
static lean_object* l_Nat_reducePow___closed__5;
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6;
static lean_object* l_Nat_reduceMul___closed__1;
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4;
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6;
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__9;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__6;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3;
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6;
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object*, lean_object*);
static lean_object* l_Nat_reduceNatEqExpr___closed__5;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12;
static lean_object* l_Nat_reduceNatEqExpr___closed__14;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__8;
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6;
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__4;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceBEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1;
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_object*);
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__5;
static lean_object* l_Nat_reduceBEq___closed__1;
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__1;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7;
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3;
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Nat_reduceGcd___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object*, lean_object*);
static lean_object* l_Nat_reduceAnd___closed__2;
static lean_object* l_Nat_reduceGT___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1;
static lean_object* l_Nat_reduceMod___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__6;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
static lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3;
static lean_object* l_Nat_reduceBoolPred___lambda__1___closed__8;
static lean_object* l_Nat_reduceShiftRight___closed__1;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12;
static lean_object* l_Nat_isValue___closed__2;
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2;
extern lean_object* l_Lean_levelOne;
static lean_object* l_Nat_reduceShiftLeft___closed__3;
static lean_object* l_Nat_reduceSucc___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceOr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__10;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5;
static lean_object* l_Nat_reduceBEq___closed__2;
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4;
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceEqDiff___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3;
static lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7;
static lean_object* l_Nat_reduceMul___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7;
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1;
static lean_object* l_Nat_reduceNatEqExpr___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1;
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__1;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__9;
static lean_object* l_Nat_reducePow___closed__4;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1;
static lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceSubDiff___lambda__1___closed__7;
static lean_object* l_Nat_reduceBNe___closed__2;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_object*);
static lean_object* l_Nat_reduceNatEqExpr___closed__7;
static lean_object* l_Nat_reducePow___closed__2;
static lean_object* l_Nat_reduceLTLE___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7;
static lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3;
static lean_object* l_Nat_reduceBNe___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5;
static lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1;
extern lean_object* l_Lean_Meta_Simp_builtinSEvalprocsRef;
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceAdd___closed__3;
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2;
static lean_object* l_Nat_reduceLT___closed__2;
static lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11;
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3;
static lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__5;
static lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1;
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_reduceNatEqExpr___closed__4;
static lean_object* l_Nat_reduceAdd___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5;
static lean_object* l_Nat_reduceBeqDiff___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_object*);
static lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1;
static lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5;
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3;
static lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6;
lean_object* lean_nat_lor(lean_object*, lean_object*);
static lean_object* l_Nat_reduceSucc___closed__1;
static lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2;
static lean_object* l_Nat_reduceNatEqExpr___closed__8;
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6;
static lean_object* l_Nat_reduceBneDiff___lambda__1___closed__7;
static lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13;
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getNatValue_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
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
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_apply_1(x_2, x_24);
x_26 = l_Lean_mkNatLit(x_25);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_apply_1(x_2, x_27);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
x_34 = lean_apply_1(x_2, x_32);
x_35 = l_Lean_mkNatLit(x_34);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_33;
 lean_ctor_set_tag(x_36, 0);
}
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
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
lean_dec(x_8);
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
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
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
lean_inc(x_7);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
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
x_25 = l_Lean_Meta_getNatValue_x3f(x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_24);
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
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_apply_2(x_2, x_23, x_36);
x_38 = l_Lean_mkNatLit(x_37);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_apply_2(x_2, x_23, x_39);
x_41 = l_Lean_mkNatLit(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_45 = x_26;
} else {
 lean_dec_ref(x_26);
 x_45 = lean_box(0);
}
x_46 = lean_apply_2(x_2, x_23, x_44);
x_47 = l_Lean_mkNatLit(x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_45;
 lean_ctor_set_tag(x_48, 0);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_8);
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
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceBin___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Nat_reduceBinPred___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_inc(x_7);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
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
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
lean_inc(x_7);
x_25 = l_Lean_Meta_getNatValue_x3f(x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_24);
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
x_29 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_apply_2(x_2, x_23, x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_37 = l_Lean_Meta_Simp_evalPropStep(x_1, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBoolPred___lambda__1___closed__1;
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_reduceBoolPred___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBoolPred___lambda__1___closed__1;
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_reduceBoolPred___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
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
x_25 = l_Lean_Meta_getNatValue_x3f(x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_24);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_apply_2(x_2, x_23, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Nat_reduceBoolPred___lambda__1___closed__5;
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; 
x_39 = l_Nat_reduceBoolPred___lambda__1___closed__9;
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_apply_2(x_2, x_23, x_41);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Nat_reduceBoolPred___lambda__1___closed__5;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Nat_reduceBoolPred___lambda__1___closed__9;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_23);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_8);
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
x_17 = l_Nat_reduceBoolPred___lambda__1(x_4, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reduceBoolPred___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_appArg_x21(x_1);
x_12 = l_Lean_Meta_getNatValue_x3f(x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
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
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_mkNatLit(x_25);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_mkNatLit(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_34 = x_13;
} else {
 lean_dec_ref(x_13);
 x_34 = lean_box(0);
}
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_33, x_35);
lean_dec(x_33);
x_37 = l_Lean_mkNatLit(x_36);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_34;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
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
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSucc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceSucc___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceSucc", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3;
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2;
x_3 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6;
x_4 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSimprocsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_builtinSEvalprocsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_add(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_add(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_add(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceAdd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceAdd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceAdd", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceSucc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2;
x_3 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12;
x_4 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_mul(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_mul(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_mul(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMul___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceMul___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceMul", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2;
x_3 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5;
x_4 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_sub(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_sub(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_sub(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSub___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceSub___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceSub", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5;
x_4 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_div(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_div(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_div(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceDiv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceDiv___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceDiv", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2;
x_3 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5;
x_4 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_mod(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_mod(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_mod(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceMod___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceMod___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceMod", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2;
x_3 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5;
x_4 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_nat_pow(x_1, x_2);
x_13 = l_Lean_mkNatLit(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Nat_reduceUnary___lambda__1___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_getNatValue_x3f(x_2, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Nat_reduceUnary___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_30);
x_31 = l_Lean_checkExponent(x_30, x_8, x_9, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = l_Nat_reduceUnary___lambda__1___closed__1;
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Nat_reduceUnary___lambda__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = l_Nat_reducePow___lambda__1(x_20, x_30, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_30);
lean_dec(x_20);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Nat_reduceUnary___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Nat_reducePow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow___lambda__2___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow___lambda__3___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reducePow___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reducePow___closed__3;
x_2 = l_Nat_reducePow___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Nat_reducePow___closed__1;
x_11 = l_Nat_reducePow___closed__2;
x_12 = l_Lean_Expr_cleanupAnnotations(x_1);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_9(x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Expr_appArg(x_12, lean_box(0));
x_17 = l_Lean_Expr_appFnCleanup(x_12, lean_box(0));
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_apply_9(x_11, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Expr_appArg(x_17, lean_box(0));
x_22 = l_Lean_Expr_appFnCleanup(x_17, lean_box(0));
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_apply_9(x_11, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup(x_22, lean_box(0));
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_16);
x_28 = lean_box(0);
x_29 = lean_apply_9(x_11, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup(x_26, lean_box(0));
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_16);
x_32 = lean_box(0);
x_33 = lean_apply_9(x_11, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Expr_appFnCleanup(x_30, lean_box(0));
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_16);
x_36 = lean_box(0);
x_37 = lean_apply_9(x_11, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Expr_appFnCleanup(x_34, lean_box(0));
x_39 = l_Nat_reducePow___closed__5;
x_40 = l_Lean_Expr_isConstOf(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
lean_dec(x_16);
x_41 = lean_box(0);
x_42 = lean_apply_9(x_11, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_apply_10(x_10, x_21, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_reducePow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reducePow___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reducePow___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reducePow", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reducePow___closed__5;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
x_2 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3;
x_2 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reducePow), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2;
x_3 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7;
x_4 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_land(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_land(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_land(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceAnd___closed__1;
x_2 = l_Nat_reduceAnd___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceAnd___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceAnd___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceAnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceAnd", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3;
x_2 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2;
x_3 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8;
x_4 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_lxor(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_lxor(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_lxor(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceXor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceXor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceXor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceXor___closed__1;
x_2 = l_Nat_reduceXor___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceXor___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceXor___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceXor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceXor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceXor", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceXor___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2;
x_3 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5;
x_4 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_lor(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_lor(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_lor(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceAnd___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceOr___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceOr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceOr", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceAnd___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2;
x_3 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5;
x_4 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_shiftl(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_shiftl(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_shiftl(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceShiftLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceShiftLeft___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceShiftLeft___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceShiftLeft___closed__1;
x_2 = l_Nat_reduceShiftLeft___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceShiftLeft___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceShiftLeft___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceShiftLeft___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceShiftLeft", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceShiftLeft___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3;
x_2 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2;
x_3 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6;
x_4 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_shiftr(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_shiftr(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_shiftr(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceShiftRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceShiftRight___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceShiftRight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceShiftRight___closed__1;
x_2 = l_Nat_reduceShiftRight___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceShiftRight___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceShiftRight___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceShiftRight___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceShiftRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceShiftRight", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceShiftRight___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3;
x_2 = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2;
x_3 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5;
x_4 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_nat_gcd(x_22, x_35);
lean_dec(x_35);
lean_dec(x_22);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_gcd(x_22, x_38);
lean_dec(x_38);
lean_dec(x_22);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = lean_nat_gcd(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_46 = l_Lean_mkNatLit(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
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
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Nat_reduceGcd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gcd", 3, 3);
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
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceGcd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceGcd", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2;
x_3 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5;
x_4 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_17 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
lean_inc(x_6);
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
x_28 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_nat_dec_lt(x_22, x_33);
lean_dec(x_33);
lean_dec(x_22);
x_35 = l_Lean_Meta_Simp_evalPropStep(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
static lean_object* _init_l_Nat_reduceLT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLT___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
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
lean_dec(x_1);
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceLT", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3() {
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
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5;
x_4 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_17 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
lean_inc(x_6);
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
x_28 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_nat_dec_lt(x_33, x_22);
lean_dec(x_22);
lean_dec(x_33);
x_35 = l_Lean_Meta_Simp_evalPropStep(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
static lean_object* _init_l_Nat_reduceGT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceGT___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
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
lean_dec(x_1);
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceGT", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2;
x_3 = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5;
x_4 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_dec_eq(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Nat_reduceBoolPred___lambda__1___closed__5;
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; 
x_37 = l_Nat_reduceBoolPred___lambda__1___closed__9;
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_nat_dec_eq(x_22, x_39);
lean_dec(x_39);
lean_dec(x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Nat_reduceBoolPred___lambda__1___closed__5;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Nat_reduceBoolPred___lambda__1___closed__9;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_22);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Nat_reduceBEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBEq___closed__1;
x_2 = l_Nat_reduceBEq___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceBEq___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceBEq___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceBEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBEq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBEq___closed__3;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2;
x_3 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5;
x_4 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_getNatValue_x3f(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
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
x_24 = l_Lean_Meta_getNatValue_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_nat_dec_eq(x_22, x_34);
lean_dec(x_34);
lean_dec(x_22);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Nat_reduceBoolPred___lambda__1___closed__9;
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; 
x_37 = l_Nat_reduceBoolPred___lambda__1___closed__5;
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_nat_dec_eq(x_22, x_39);
lean_dec(x_39);
lean_dec(x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Nat_reduceBoolPred___lambda__1___closed__9;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Nat_reduceBoolPred___lambda__1___closed__5;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_22);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Nat_reduceBNe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bne", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBNe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBNe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceBNe___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_16 = l_Nat_reduceBNe___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceBNe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBNe", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBNe___closed__2;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2;
x_3 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5;
x_4 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Nat_isValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Nat_isValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Nat_isValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_isValue___closed__1;
x_2 = l_Nat_isValue___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Nat_reducePow___closed__2;
x_14 = l_Lean_Expr_cleanupAnnotations(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_9(x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup(x_14, lean_box(0));
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_9(x_13, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_apply_9(x_13, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appFnCleanup(x_22, lean_box(0));
x_27 = l_Nat_isValue___closed__3;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_apply_9(x_13, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Nat_isValue___lambda__1(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
}
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
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isValue", 7, 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_isValue___closed__3;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3;
x_2 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_isValue), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2;
x_3 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6;
x_4 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_2);
x_14 = l_Lean_Meta_getNatValue_x3f(x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
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
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_15, 0, x_26);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceAdd___closed__3;
x_11 = lean_unsigned_to_nat(6u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3;
x_14 = lean_unsigned_to_nat(4u);
x_15 = l_Lean_Expr_isAppOfArity(x_1, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4;
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Expr_isAppOfArity(x_1, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = l_Nat_reduceSucc___closed__3;
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Expr_isAppOfArity(x_1, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Expr_appArg_x21(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Expr_appFn_x21(x_1);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_Lean_Meta_getNatValue_x3f(x_30, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
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
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_32, 0, x_43);
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_49 = x_32;
} else {
 lean_dec_ref(x_32);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_29);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Lean_Expr_appFn_x21(x_1);
x_58 = l_Lean_Expr_appFn_x21(x_57);
x_59 = l_Lean_Expr_appArg_x21(x_58);
lean_dec(x_58);
x_60 = l_Lean_Nat_mkInstAdd;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_61 = l_Lean_Meta_matchesInstance(x_59, x_60, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1(x_57, x_1, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_57);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lean_Expr_appFn_x21(x_1);
x_78 = l_Lean_Expr_appFn_x21(x_77);
x_79 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_80 = l_Lean_Nat_mkInstHAdd;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Meta_matchesInstance(x_79, x_80, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_81, 0, x_86);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_box(0);
x_92 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1(x_77, x_1, x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_77);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_81);
if (x_93 == 0)
{
return x_81;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_81, 0);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_nat_add(x_2, x_32);
lean_dec(x_32);
lean_dec(x_2);
x_1 = x_31;
x_2 = x_33;
x_10 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_27);
x_28 = l_Lean_mkNatLit(x_27);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_15, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_33);
x_34 = l_Lean_mkNatLit(x_33);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_15, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_39 = x_14;
} else {
 lean_dec_ref(x_14);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
lean_inc(x_41);
x_42 = l_Lean_mkNatLit(x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_39;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_nat_add(x_53, x_2);
lean_dec(x_2);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_12, 0, x_55);
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_12, 0);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_nat_add(x_56, x_2);
lean_dec(x_2);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_11, 0, x_59);
return x_11;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = lean_ctor_get(x_12, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_62 = x_12;
} else {
 lean_dec_ref(x_12);
 x_62 = lean_box(0);
}
x_63 = lean_nat_add(x_61, x_2);
lean_dec(x_2);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
return x_11;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_11, 0);
x_69 = lean_ctor_get(x_11, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_11);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instHAdd", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instAddNat", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_levelZero;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_levelZero;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceAdd___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15;
x_14 = l_Lean_mkAppN(x_13, x_12);
lean_dec(x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instSubNat", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instHSub", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSub___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11;
x_14 = l_Lean_mkAppN(x_13, x_12);
lean_dec(x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_array_mk(x_7);
x_9 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4;
x_10 = l_Lean_mkAppN(x_9, x_8);
lean_dec(x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instBEqOfDecidableEq", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instDecidableEqNat", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBEq___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_mk(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1;
x_12 = l_Lean_mkAppN(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceBNe___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_mk(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1;
x_12 = l_Lean_mkAppN(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLENat", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_mk(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4;
x_12 = l_Lean_mkAppN(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceLT___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_mk(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1;
x_12 = l_Lean_mkAppN(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Nat_reduceBoolPred___lambda__1___closed__8;
x_12 = l_Lean_Meta_mkEqRefl(x_11, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3;
x_21 = l_Lean_mkAppN(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3;
x_30 = l_Lean_mkAppN(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = l_Lean_mkAppN(x_14, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_12);
x_19 = lean_box(0);
x_20 = l_Nat_applySimprocConst___lambda__1(x_2, x_3, x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Environment_contains(x_23, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Nat_applySimprocConst___lambda__1(x_2, x_3, x_1, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_applySimprocConst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applySimprocConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = l_Lean_mkAppN(x_14, x_2);
x_16 = lean_apply_1(x_3, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_12);
x_19 = lean_box(0);
x_20 = l_Nat_applyEqLemma___lambda__1(x_2, x_3, x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Environment_contains(x_23, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Nat_applyEqLemma___lambda__1(x_2, x_3, x_1, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_applyEqLemma___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_applyEqLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_sub(x_1, x_2);
x_6 = l_Lean_mkNatLit(x_5);
x_7 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simproc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_add_gt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_add_le", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_eq_gt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_eq_le", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_eq_add_ge", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__11;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_eq_add_le", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceNatEqExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceNatEqExpr___closed__13;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_22 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_22, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_37, 0, x_36);
lean_ctor_set(x_23, 0, x_37);
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_42, 0, x_41);
lean_ctor_set(x_23, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_23);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_dec(x_22);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_31, 2);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_dec_le(x_48, x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_45);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_1, x_47);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_50, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_mk(x_58);
x_60 = l_Nat_reduceNatEqExpr___closed__4;
x_61 = l_Nat_reduceNatEqExpr___closed__3;
x_62 = l_Nat_applyEqLemma(x_60, x_61, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_59);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_inc(x_1);
lean_inc(x_47);
x_67 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_47, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_67, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_46);
x_71 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__2___boxed), 4, 3);
lean_closure_set(x_71, 0, x_45);
lean_closure_set(x_71, 1, x_48);
lean_closure_set(x_71, 2, x_46);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_47);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_46);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_array_mk(x_76);
x_78 = l_Nat_reduceNatEqExpr___closed__6;
x_79 = l_Nat_applyEqLemma(x_71, x_78, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_77);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_68);
if (x_80 == 0)
{
return x_68;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_68, 0);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_23, 0);
lean_inc(x_84);
lean_dec(x_23);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_85 = lean_ctor_get(x_22, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_86 = x_22;
} else {
 lean_dec_ref(x_22);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_21, 0);
lean_inc(x_87);
lean_dec(x_21);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_85);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_22, 1);
lean_inc(x_93);
lean_dec(x_22);
x_94 = lean_ctor_get(x_21, 0);
lean_inc(x_94);
lean_dec(x_21);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_84, 2);
lean_inc(x_97);
lean_dec(x_84);
x_98 = lean_nat_dec_le(x_97, x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_94);
lean_inc(x_96);
lean_inc(x_1);
x_99 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_1, x_96);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_100 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_99, x_6, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_mk(x_107);
x_109 = l_Nat_reduceNatEqExpr___closed__4;
x_110 = l_Nat_reduceNatEqExpr___closed__3;
x_111 = l_Nat_applyEqLemma(x_109, x_110, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_114 = x_100;
} else {
 lean_dec_ref(x_100);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_inc(x_1);
lean_inc(x_96);
x_116 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_96, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_117 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_116, x_6, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_95);
x_120 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__2___boxed), 4, 3);
lean_closure_set(x_120, 0, x_94);
lean_closure_set(x_120, 1, x_97);
lean_closure_set(x_120, 2, x_95);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_96);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_95);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_mk(x_125);
x_127 = l_Nat_reduceNatEqExpr___closed__6;
x_128 = l_Nat_applyEqLemma(x_120, x_127, x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_119);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_117, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_131 = x_117;
} else {
 lean_dec_ref(x_117);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_1);
x_133 = lean_ctor_get(x_23, 0);
lean_inc(x_133);
lean_dec(x_23);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_22, 1);
lean_inc(x_134);
lean_dec(x_22);
x_135 = lean_ctor_get(x_21, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_21, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_21, 2);
lean_inc(x_137);
lean_dec(x_21);
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_nat_dec_le(x_137, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_137);
lean_inc(x_136);
lean_inc(x_2);
x_140 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_2, x_136);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_141 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_140, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_135);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_mk(x_148);
x_150 = l_Nat_reduceNatEqExpr___closed__4;
x_151 = l_Nat_reduceNatEqExpr___closed__8;
x_152 = l_Nat_applyEqLemma(x_150, x_151, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_143);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_149);
return x_152;
}
else
{
uint8_t x_153; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_141);
if (x_153 == 0)
{
return x_141;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_141, 0);
x_155 = lean_ctor_get(x_141, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_141);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_inc(x_2);
lean_inc(x_136);
x_157 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_136, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_158 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_157, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_135);
x_161 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__2___boxed), 4, 3);
lean_closure_set(x_161, 0, x_138);
lean_closure_set(x_161, 1, x_137);
lean_closure_set(x_161, 2, x_135);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_2);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_136);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_135);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_mk(x_166);
x_168 = l_Nat_reduceNatEqExpr___closed__10;
x_169 = l_Nat_applyEqLemma(x_161, x_168, x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_160);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_167);
return x_169;
}
else
{
uint8_t x_170; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_158);
if (x_170 == 0)
{
return x_158;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_158, 0);
x_172 = lean_ctor_get(x_158, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_158);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_dec(x_2);
x_174 = lean_ctor_get(x_22, 1);
lean_inc(x_174);
lean_dec(x_22);
x_175 = lean_ctor_get(x_21, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_21, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_21, 2);
lean_inc(x_177);
lean_dec(x_21);
x_178 = lean_ctor_get(x_133, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_133, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_133, 2);
lean_inc(x_180);
lean_dec(x_133);
x_181 = lean_nat_dec_le(x_177, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_nat_sub(x_177, x_180);
lean_dec(x_180);
lean_dec(x_177);
x_183 = l_Lean_mkNatLit(x_182);
lean_inc(x_175);
x_184 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_175, x_183);
lean_inc(x_176);
lean_inc(x_179);
x_185 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_179, x_176);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_186 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_185, x_6, x_7, x_8, x_9, x_174);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_178);
x_189 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__3), 3, 2);
lean_closure_set(x_189, 0, x_184);
lean_closure_set(x_189, 1, x_178);
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_179);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_176);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_175);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_array_mk(x_195);
x_197 = l_Nat_reduceNatEqExpr___closed__12;
x_198 = l_Nat_applyEqLemma(x_189, x_197, x_196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_188);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_196);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_199 = !lean_is_exclusive(x_186);
if (x_199 == 0)
{
return x_186;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_186, 0);
x_201 = lean_ctor_get(x_186, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_186);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; lean_object* x_204; 
x_203 = lean_nat_dec_eq(x_177, x_180);
lean_inc(x_179);
lean_inc(x_176);
x_204 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_176, x_179);
if (x_203 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_nat_sub(x_180, x_177);
lean_dec(x_177);
lean_dec(x_180);
x_206 = l_Lean_mkNatLit(x_205);
lean_inc(x_178);
x_207 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_178, x_206);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_208 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_204, x_6, x_7, x_8, x_9, x_174);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_175);
x_211 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__3), 3, 2);
lean_closure_set(x_211, 0, x_175);
lean_closure_set(x_211, 1, x_207);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_179);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_176);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_178);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_175);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_array_mk(x_217);
x_219 = l_Nat_reduceNatEqExpr___closed__14;
x_220 = l_Nat_applyEqLemma(x_211, x_219, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_210);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_218);
return x_220;
}
else
{
uint8_t x_221; 
lean_dec(x_207);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_221 = !lean_is_exclusive(x_208);
if (x_221 == 0)
{
return x_208;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_208, 0);
x_223 = lean_ctor_get(x_208, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_208);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; 
lean_dec(x_180);
lean_dec(x_177);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_225 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_204, x_6, x_7, x_8, x_9, x_174);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
lean_inc(x_178);
lean_inc(x_175);
x_228 = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___lambda__3), 3, 2);
lean_closure_set(x_228, 0, x_175);
lean_closure_set(x_228, 1, x_178);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_179);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_176);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_178);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_175);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_array_mk(x_234);
x_236 = l_Nat_reduceNatEqExpr___closed__14;
x_237 = l_Nat_applyEqLemma(x_228, x_236, x_235, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_227);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_235);
return x_237;
}
else
{
uint8_t x_238; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_238 = !lean_is_exclusive(x_225);
if (x_238 == 0)
{
return x_225;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_225, 0);
x_240 = lean_ctor_get(x_225, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_225);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
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
uint8_t x_242; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_22);
if (x_242 == 0)
{
return x_22;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_22, 0);
x_244 = lean_ctor_get(x_22, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_22);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_12);
if (x_246 == 0)
{
return x_12;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_12, 0);
x_248 = lean_ctor_get(x_12, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_12);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_reduceNatEqExpr___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceNatEqExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Nat_reduceNatEqExpr(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_26 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = l_Nat_reduceBoolPred___lambda__1___closed__4;
x_31 = l_Lean_Meta_mkEqRefl(x_30, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_mk(x_37);
x_39 = l_Nat_reduceEqDiff___lambda__1___closed__3;
x_40 = l_Lean_mkAppN(x_39, x_38);
lean_dec(x_38);
lean_ctor_set(x_15, 0, x_40);
x_41 = l_Nat_reduceEqDiff___lambda__1___closed__6;
x_42 = 1;
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_15);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_31, 0, x_44);
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_29);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_mk(x_50);
x_52 = l_Nat_reduceEqDiff___lambda__1___closed__3;
x_53 = l_Lean_mkAppN(x_52, x_51);
lean_dec(x_51);
lean_ctor_set(x_15, 0, x_53);
x_54 = l_Nat_reduceEqDiff___lambda__1___closed__6;
x_55 = 1;
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_15);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_46);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
lean_free_object(x_15);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_31);
if (x_59 == 0)
{
return x_31;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_31, 0);
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_31);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_26);
if (x_63 == 0)
{
return x_26;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_68 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = l_Nat_reduceBoolPred___lambda__1___closed__8;
x_73 = l_Lean_Meta_mkEqRefl(x_72, x_6, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_71);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_array_mk(x_79);
x_81 = l_Nat_reduceEqDiff___lambda__1___closed__9;
x_82 = l_Lean_mkAppN(x_81, x_80);
lean_dec(x_80);
lean_ctor_set(x_15, 0, x_82);
x_83 = l_Nat_reduceEqDiff___lambda__1___closed__12;
x_84 = 1;
x_85 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_15);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_71);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_mk(x_92);
x_94 = l_Nat_reduceEqDiff___lambda__1___closed__9;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_dec(x_93);
lean_ctor_set(x_15, 0, x_95);
x_96 = l_Nat_reduceEqDiff___lambda__1___closed__12;
x_97 = 1;
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_15);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_97);
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
lean_dec(x_69);
lean_free_object(x_15);
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
else
{
uint8_t x_105; 
lean_free_object(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_68);
if (x_105 == 0)
{
return x_68;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_68, 0);
x_107 = lean_ctor_get(x_68, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_68);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
case 1:
{
uint8_t x_109; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_14);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_14, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_23);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_15, 0, x_112);
x_113 = l_Nat_reduceEqDiff___lambda__1___closed__13;
x_114 = 1;
x_115 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_15);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_114);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_115);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_23, 0);
lean_inc(x_116);
lean_dec(x_23);
lean_ctor_set(x_15, 0, x_116);
x_117 = l_Nat_reduceEqDiff___lambda__1___closed__13;
x_118 = 1;
x_119 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_15);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_14, 0, x_120);
return x_14;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_14, 1);
lean_inc(x_121);
lean_dec(x_14);
x_122 = lean_ctor_get(x_23, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_123 = x_23;
} else {
 lean_dec_ref(x_23);
 x_123 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_122);
x_124 = l_Nat_reduceEqDiff___lambda__1___closed__13;
x_125 = 1;
x_126 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_15);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_125);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_123;
 lean_ctor_set_tag(x_127, 0);
}
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_121);
return x_128;
}
}
default: 
{
uint8_t x_129; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_14);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_14, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_23, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_23, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_23, 2);
lean_inc(x_133);
lean_dec(x_23);
x_134 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_131, x_132);
lean_ctor_set(x_15, 0, x_133);
x_135 = 1;
x_136 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_15);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_14, 0, x_137);
return x_14;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_14, 1);
lean_inc(x_138);
lean_dec(x_14);
x_139 = lean_ctor_get(x_23, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_23, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_23, 2);
lean_inc(x_141);
lean_dec(x_23);
x_142 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_139, x_140);
lean_ctor_set(x_15, 0, x_141);
x_143 = 1;
x_144 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_15);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_138);
return x_146;
}
}
}
}
else
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_15, 0);
lean_inc(x_147);
lean_dec(x_15);
switch (lean_obj_tag(x_147)) {
case 0:
{
uint8_t x_148; 
x_148 = lean_ctor_get_uint8(x_147, 0);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_14, 1);
lean_inc(x_149);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_150 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_box(0);
x_154 = l_Nat_reduceBoolPred___lambda__1___closed__4;
x_155 = l_Lean_Meta_mkEqRefl(x_154, x_6, x_7, x_8, x_9, x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Expr_appArg_x21(x_151);
lean_dec(x_151);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_153);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_mk(x_162);
x_164 = l_Nat_reduceEqDiff___lambda__1___closed__3;
x_165 = l_Lean_mkAppN(x_164, x_163);
lean_dec(x_163);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_Nat_reduceEqDiff___lambda__1___closed__6;
x_168 = 1;
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_168);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
if (lean_is_scalar(x_158)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_158;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_157);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_151);
lean_dec(x_1);
x_172 = lean_ctor_get(x_155, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_155, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_174 = x_155;
} else {
 lean_dec_ref(x_155);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_176 = lean_ctor_get(x_150, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_150, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_178 = x_150;
} else {
 lean_dec_ref(x_150);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_14, 1);
lean_inc(x_180);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_181 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_box(0);
x_185 = l_Nat_reduceBoolPred___lambda__1___closed__8;
x_186 = l_Lean_Meta_mkEqRefl(x_185, x_6, x_7, x_8, x_9, x_183);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = l_Lean_Expr_appArg_x21(x_182);
lean_dec(x_182);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_184);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_1);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_array_mk(x_193);
x_195 = l_Nat_reduceEqDiff___lambda__1___closed__9;
x_196 = l_Lean_mkAppN(x_195, x_194);
lean_dec(x_194);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l_Nat_reduceEqDiff___lambda__1___closed__12;
x_199 = 1;
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_197);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_199);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
if (lean_is_scalar(x_189)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_189;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_188);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_182);
lean_dec(x_1);
x_203 = lean_ctor_get(x_186, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_186, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_205 = x_186;
} else {
 lean_dec_ref(x_186);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_207 = lean_ctor_get(x_181, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_181, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_209 = x_181;
} else {
 lean_dec_ref(x_181);
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
}
case 1:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_211 = lean_ctor_get(x_14, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_212 = x_14;
} else {
 lean_dec_ref(x_14);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_147, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_214 = x_147;
} else {
 lean_dec_ref(x_147);
 x_214 = lean_box(0);
}
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_213);
x_216 = l_Nat_reduceEqDiff___lambda__1___closed__13;
x_217 = 1;
x_218 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_215);
lean_ctor_set_uint8(x_218, sizeof(void*)*2, x_217);
if (lean_is_scalar(x_214)) {
 x_219 = lean_alloc_ctor(0, 1, 0);
} else {
 x_219 = x_214;
 lean_ctor_set_tag(x_219, 0);
}
lean_ctor_set(x_219, 0, x_218);
if (lean_is_scalar(x_212)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_212;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
default: 
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_221 = lean_ctor_get(x_14, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_222 = x_14;
} else {
 lean_dec_ref(x_14);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_147, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_147, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_147, 2);
lean_inc(x_225);
lean_dec(x_147);
x_226 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(x_223, x_224);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_225);
x_228 = 1;
x_229 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_228);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
if (lean_is_scalar(x_222)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_222;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_221);
return x_231;
}
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_14);
if (x_232 == 0)
{
return x_14;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_14, 0);
x_234 = lean_ctor_get(x_14, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_14);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceEqDiff___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceEqDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceEqDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceEqDiff", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3;
x_2 = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2;
x_3 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5;
x_4 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__4;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_reduceBeqDiff___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__8;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_reduceBeqDiff___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beqFalseOfEqFalse", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceBeqDiff___lambda__1___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBeqDiff___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beqEqOfEqEq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceBeqDiff___lambda__1___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBeqDiff___lambda__1___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Nat_reduceNatEqExpr(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_24; 
lean_free_object(x_15);
lean_dec(x_13);
lean_dec(x_12);
x_24 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_dec(x_32);
x_33 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_14, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_mk(x_44);
x_46 = l_Nat_reduceBeqDiff___lambda__1___closed__7;
x_47 = l_Lean_mkAppN(x_46, x_45);
lean_dec(x_45);
lean_ctor_set(x_15, 0, x_47);
x_48 = l_Nat_reduceBeqDiff___lambda__1___closed__8;
x_49 = 1;
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_15);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_49);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_50);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
x_57 = l_Nat_reduceBeqDiff___lambda__1___closed__7;
x_58 = l_Lean_mkAppN(x_57, x_56);
lean_dec(x_56);
lean_ctor_set(x_15, 0, x_58);
x_59 = l_Nat_reduceBeqDiff___lambda__1___closed__8;
x_60 = 1;
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_15);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_14, 0, x_62);
return x_14;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_dec(x_14);
x_64 = lean_ctor_get(x_23, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_65 = x_23;
} else {
 lean_dec_ref(x_23);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_13);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_mk(x_69);
x_71 = l_Nat_reduceBeqDiff___lambda__1___closed__7;
x_72 = l_Lean_mkAppN(x_71, x_70);
lean_dec(x_70);
lean_ctor_set(x_15, 0, x_72);
x_73 = l_Nat_reduceBeqDiff___lambda__1___closed__8;
x_74 = 1;
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_15);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_74);
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_65;
 lean_ctor_set_tag(x_76, 0);
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
return x_77;
}
}
default: 
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_79 = lean_ctor_get(x_14, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_23, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_23, 2);
lean_inc(x_82);
lean_dec(x_23);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_80);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_13);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_mk(x_88);
x_90 = l_Nat_reduceBeqDiff___lambda__1___closed__11;
x_91 = l_Lean_mkAppN(x_90, x_89);
lean_dec(x_89);
x_92 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(x_80, x_81);
lean_ctor_set(x_15, 0, x_91);
x_93 = 1;
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_15);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_14, 0, x_95);
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_96 = lean_ctor_get(x_14, 1);
lean_inc(x_96);
lean_dec(x_14);
x_97 = lean_ctor_get(x_23, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_23, 2);
lean_inc(x_99);
lean_dec(x_23);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_97);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_12);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_mk(x_105);
x_107 = l_Nat_reduceBeqDiff___lambda__1___closed__11;
x_108 = l_Lean_mkAppN(x_107, x_106);
lean_dec(x_106);
x_109 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(x_97, x_98);
lean_ctor_set(x_15, 0, x_108);
x_110 = 1;
x_111 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_15);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_96);
return x_113;
}
}
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_15, 0);
lean_inc(x_114);
lean_dec(x_15);
switch (lean_obj_tag(x_114)) {
case 0:
{
uint8_t x_115; 
lean_dec(x_13);
lean_dec(x_12);
x_115 = lean_ctor_get_uint8(x_114, 0);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_14, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_117 = x_14;
} else {
 lean_dec_ref(x_14);
 x_117 = lean_box(0);
}
x_118 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_14, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_121 = x_14;
} else {
 lean_dec_ref(x_14);
 x_121 = lean_box(0);
}
x_122 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
case 1:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_124 = lean_ctor_get(x_14, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_125 = x_14;
} else {
 lean_dec_ref(x_14);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_13);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_12);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_mk(x_131);
x_133 = l_Nat_reduceBeqDiff___lambda__1___closed__7;
x_134 = l_Lean_mkAppN(x_133, x_132);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Nat_reduceBeqDiff___lambda__1___closed__8;
x_137 = 1;
x_138 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*2, x_137);
if (lean_is_scalar(x_127)) {
 x_139 = lean_alloc_ctor(0, 1, 0);
} else {
 x_139 = x_127;
 lean_ctor_set_tag(x_139, 0);
}
lean_ctor_set(x_139, 0, x_138);
if (lean_is_scalar(x_125)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_125;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_124);
return x_140;
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_141 = lean_ctor_get(x_14, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_142 = x_14;
} else {
 lean_dec_ref(x_14);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_114, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_114, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_114, 2);
lean_inc(x_145);
lean_dec(x_114);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_143);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_13);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_12);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_mk(x_151);
x_153 = l_Nat_reduceBeqDiff___lambda__1___closed__11;
x_154 = l_Lean_mkAppN(x_153, x_152);
lean_dec(x_152);
x_155 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(x_143, x_144);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_154);
x_157 = 1;
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
if (lean_is_scalar(x_142)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_142;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_141);
return x_160;
}
}
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_13);
lean_dec(x_12);
x_161 = !lean_is_exclusive(x_14);
if (x_161 == 0)
{
return x_14;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_14, 0);
x_163 = lean_ctor_get(x_14, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_14);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceBEq___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceBeqDiff___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceBeqDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBeqDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBeqDiff", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2;
x_3 = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5;
x_4 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bneTrueOfEqFalse", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceBneDiff___lambda__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBneDiff___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBoolPred___lambda__1___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bneEqOfEqEq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceBneDiff___lambda__1___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceBneDiff___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Nat_reduceNatEqExpr(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_24; 
lean_free_object(x_15);
lean_dec(x_13);
lean_dec(x_12);
x_24 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_dec(x_32);
x_33 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_14, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_mk(x_44);
x_46 = l_Nat_reduceBneDiff___lambda__1___closed__3;
x_47 = l_Lean_mkAppN(x_46, x_45);
lean_dec(x_45);
lean_ctor_set(x_15, 0, x_47);
x_48 = l_Nat_reduceBneDiff___lambda__1___closed__4;
x_49 = 1;
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_15);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_49);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_50);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
x_57 = l_Nat_reduceBneDiff___lambda__1___closed__3;
x_58 = l_Lean_mkAppN(x_57, x_56);
lean_dec(x_56);
lean_ctor_set(x_15, 0, x_58);
x_59 = l_Nat_reduceBneDiff___lambda__1___closed__4;
x_60 = 1;
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_15);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_14, 0, x_62);
return x_14;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_dec(x_14);
x_64 = lean_ctor_get(x_23, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_65 = x_23;
} else {
 lean_dec_ref(x_23);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_13);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_mk(x_69);
x_71 = l_Nat_reduceBneDiff___lambda__1___closed__3;
x_72 = l_Lean_mkAppN(x_71, x_70);
lean_dec(x_70);
lean_ctor_set(x_15, 0, x_72);
x_73 = l_Nat_reduceBneDiff___lambda__1___closed__4;
x_74 = 1;
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_15);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_74);
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_65;
 lean_ctor_set_tag(x_76, 0);
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
return x_77;
}
}
default: 
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_79 = lean_ctor_get(x_14, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_23, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_23, 2);
lean_inc(x_82);
lean_dec(x_23);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_80);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_13);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_mk(x_88);
x_90 = l_Nat_reduceBneDiff___lambda__1___closed__7;
x_91 = l_Lean_mkAppN(x_90, x_89);
lean_dec(x_89);
x_92 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(x_80, x_81);
lean_ctor_set(x_15, 0, x_91);
x_93 = 1;
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_15);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_14, 0, x_95);
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_96 = lean_ctor_get(x_14, 1);
lean_inc(x_96);
lean_dec(x_14);
x_97 = lean_ctor_get(x_23, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_23, 2);
lean_inc(x_99);
lean_dec(x_23);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_97);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_12);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_mk(x_105);
x_107 = l_Nat_reduceBneDiff___lambda__1___closed__7;
x_108 = l_Lean_mkAppN(x_107, x_106);
lean_dec(x_106);
x_109 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(x_97, x_98);
lean_ctor_set(x_15, 0, x_108);
x_110 = 1;
x_111 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_15);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_96);
return x_113;
}
}
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_15, 0);
lean_inc(x_114);
lean_dec(x_15);
switch (lean_obj_tag(x_114)) {
case 0:
{
uint8_t x_115; 
lean_dec(x_13);
lean_dec(x_12);
x_115 = lean_ctor_get_uint8(x_114, 0);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_14, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_117 = x_14;
} else {
 lean_dec_ref(x_14);
 x_117 = lean_box(0);
}
x_118 = l_Nat_reduceBeqDiff___lambda__1___closed__4;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_14, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_121 = x_14;
} else {
 lean_dec_ref(x_14);
 x_121 = lean_box(0);
}
x_122 = l_Nat_reduceBeqDiff___lambda__1___closed__2;
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
case 1:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_124 = lean_ctor_get(x_14, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_125 = x_14;
} else {
 lean_dec_ref(x_14);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_13);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_12);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_mk(x_131);
x_133 = l_Nat_reduceBneDiff___lambda__1___closed__3;
x_134 = l_Lean_mkAppN(x_133, x_132);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Nat_reduceBneDiff___lambda__1___closed__4;
x_137 = 1;
x_138 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*2, x_137);
if (lean_is_scalar(x_127)) {
 x_139 = lean_alloc_ctor(0, 1, 0);
} else {
 x_139 = x_127;
 lean_ctor_set_tag(x_139, 0);
}
lean_ctor_set(x_139, 0, x_138);
if (lean_is_scalar(x_125)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_125;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_124);
return x_140;
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_141 = lean_ctor_get(x_14, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_142 = x_14;
} else {
 lean_dec_ref(x_14);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_114, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_114, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_114, 2);
lean_inc(x_145);
lean_dec(x_114);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_143);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_13);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_12);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_mk(x_151);
x_153 = l_Nat_reduceBneDiff___lambda__1___closed__7;
x_154 = l_Lean_mkAppN(x_153, x_152);
lean_dec(x_152);
x_155 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(x_143, x_144);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_154);
x_157 = 1;
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
if (lean_is_scalar(x_142)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_142;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_141);
return x_160;
}
}
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_13);
lean_dec(x_12);
x_161 = !lean_is_exclusive(x_14);
if (x_161 == 0)
{
return x_14;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_14, 0);
x_163 = lean_ctor_get(x_14, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_14);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Nat_reduceBNe___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceBneDiff___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceBneDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceBneDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBneDiff", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2;
x_3 = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5;
x_4 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_add_ge", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Nat_reduceEqDiff___lambda__1___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_add_le", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_le_gt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_le_le", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__8;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_le_add_ge", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__10;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_le_add_le", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceLTLE___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceLTLE___lambda__1___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_1);
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_unsigned_to_nat(0u);
x_15 = x_203;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = lean_unsigned_to_nat(1u);
x_15 = x_204;
goto block_202;
}
block_202:
{
lean_object* x_16; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_16 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_27 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_14, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_35; 
lean_dec(x_14);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_40 = l_Lean_Meta_Simp_evalPropStep(x_1, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 2);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_nat_dec_le(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_nat_sub(x_42, x_45);
lean_dec(x_45);
lean_dec(x_42);
x_48 = l_Lean_mkNatLit(x_47);
lean_inc(x_43);
x_49 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_48, x_43);
lean_inc(x_13);
lean_inc(x_44);
x_50 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_44, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_50, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_mk(x_58);
x_60 = l_Nat_reduceLTLE___lambda__1___closed__2;
x_61 = l_Nat_applySimprocConst(x_49, x_60, x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_59);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_62 = !lean_is_exclusive(x_51);
if (x_62 == 0)
{
return x_51;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_51, 0);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_51);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_45);
lean_dec(x_42);
lean_inc(x_44);
lean_inc(x_13);
x_66 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_13, x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_67 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_66, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_44);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_43);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_13);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_mk(x_74);
x_76 = l_Nat_reduceLTLE___lambda__1___closed__3;
x_77 = l_Nat_reduceLTLE___lambda__1___closed__5;
x_78 = l_Nat_applySimprocConst(x_76, x_77, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_75);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_67);
if (x_79 == 0)
{
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_67, 0);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_67);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_13);
lean_dec(x_1);
x_83 = lean_ctor_get(x_28, 0);
lean_inc(x_83);
lean_dec(x_28);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_27, 1);
lean_inc(x_84);
lean_dec(x_27);
x_85 = lean_ctor_get(x_25, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 2);
lean_inc(x_87);
lean_dec(x_25);
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
lean_dec(x_87);
lean_inc(x_86);
lean_inc(x_14);
x_90 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(x_14, x_86);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_91 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_90, x_7, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_14);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_85);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_mk(x_98);
x_100 = l_Nat_reduceEqDiff___lambda__1___closed__13;
x_101 = l_Nat_reduceLTLE___lambda__1___closed__7;
x_102 = l_Nat_applySimprocConst(x_100, x_101, x_99, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_99);
return x_102;
}
else
{
uint8_t x_103; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
return x_91;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_nat_sub(x_88, x_87);
lean_dec(x_87);
lean_dec(x_88);
x_108 = l_Lean_mkNatLit(x_107);
lean_inc(x_85);
x_109 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_85, x_108);
lean_inc(x_14);
lean_inc(x_86);
x_110 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_86, x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_111 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_110, x_7, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_14);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_86);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_85);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_mk(x_118);
x_120 = l_Nat_reduceLTLE___lambda__1___closed__9;
x_121 = l_Nat_applySimprocConst(x_109, x_120, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_119);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_109);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_122 = !lean_is_exclusive(x_111);
if (x_122 == 0)
{
return x_111;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_111, 0);
x_124 = lean_ctor_get(x_111, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_111);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_14);
x_126 = lean_ctor_get(x_27, 1);
lean_inc(x_126);
lean_dec(x_27);
x_127 = lean_ctor_get(x_25, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_25, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_25, 2);
lean_inc(x_129);
lean_dec(x_25);
x_130 = lean_ctor_get(x_83, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_83, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_83, 2);
lean_inc(x_132);
lean_dec(x_83);
x_133 = lean_nat_dec_le(x_129, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_nat_sub(x_129, x_132);
lean_dec(x_132);
lean_dec(x_129);
x_135 = l_Lean_mkNatLit(x_134);
lean_inc(x_127);
x_136 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_127, x_135);
lean_inc(x_130);
x_137 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_136, x_130);
lean_inc(x_128);
lean_inc(x_131);
x_138 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_131, x_128);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_139 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_138, x_7, x_8, x_9, x_10, x_126);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_131);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_128);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_130);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_127);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_mk(x_147);
x_149 = l_Nat_reduceLTLE___lambda__1___closed__11;
x_150 = l_Nat_applySimprocConst(x_137, x_149, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_148);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_137);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_151 = !lean_is_exclusive(x_139);
if (x_151 == 0)
{
return x_139;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_139, 0);
x_153 = lean_ctor_get(x_139, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_139);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; lean_object* x_156; 
x_155 = lean_nat_dec_eq(x_129, x_132);
lean_inc(x_131);
lean_inc(x_128);
x_156 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_128, x_131);
if (x_155 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_nat_sub(x_132, x_129);
lean_dec(x_129);
lean_dec(x_132);
x_158 = l_Lean_mkNatLit(x_157);
lean_inc(x_130);
x_159 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_130, x_158);
lean_inc(x_127);
x_160 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_127, x_159);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_161 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_156, x_7, x_8, x_9, x_10, x_126);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_131);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_128);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_130);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_127);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_mk(x_169);
x_171 = l_Nat_reduceLTLE___lambda__1___closed__13;
x_172 = l_Nat_applySimprocConst(x_160, x_171, x_170, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_163);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_170);
return x_172;
}
else
{
uint8_t x_173; 
lean_dec(x_160);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_173 = !lean_is_exclusive(x_161);
if (x_173 == 0)
{
return x_161;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_161, 0);
x_175 = lean_ctor_get(x_161, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_161);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_132);
lean_dec(x_129);
lean_inc(x_130);
lean_inc(x_127);
x_177 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_127, x_130);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_178 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_156, x_7, x_8, x_9, x_10, x_126);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_131);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_128);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_130);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_127);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_array_mk(x_186);
x_188 = l_Nat_reduceLTLE___lambda__1___closed__13;
x_189 = l_Nat_applySimprocConst(x_177, x_188, x_187, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_180);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_187);
return x_189;
}
else
{
uint8_t x_190; 
lean_dec(x_177);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_190 = !lean_is_exclusive(x_178);
if (x_190 == 0)
{
return x_178;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_178, 0);
x_192 = lean_ctor_get(x_178, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_178);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
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
uint8_t x_194; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_27);
if (x_194 == 0)
{
return x_27;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_27, 0);
x_196 = lean_ctor_get(x_27, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_27);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_16);
if (x_198 == 0)
{
return x_16;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_16, 0);
x_200 = lean_ctor_get(x_16, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_16);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_8);
lean_dec(x_4);
x_14 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Nat_reduceLTLE___lambda__1(x_4, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Nat_reduceLTLE___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Nat_reduceLTLE(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3;
x_11 = lean_unsigned_to_nat(4u);
x_12 = 0;
x_13 = l_Nat_reduceLTLE(x_10, x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceLeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceLeDiff", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3;
x_2 = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2;
x_3 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5;
x_4 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sub_add_eq_comm", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceSubDiff___lambda__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_sub_assoc", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceSubDiff___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_sub_le", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceSubDiff___lambda__1___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_sub_add_ge", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceSubDiff___lambda__1___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add_sub_add_le", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l_Nat_reduceNatEqExpr___closed__1;
x_3 = l_Nat_reduceSubDiff___lambda__1___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Nat_reduceBinPred___lambda__1___closed__1;
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
x_25 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(x_24, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_Nat_reduceBinPred___lambda__1___closed__1;
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_33; 
lean_dec(x_24);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_12);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_nat_sub(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
x_40 = l_Lean_mkNatLit(x_39);
lean_inc(x_40);
x_41 = l_Lean_Meta_mkEqRefl(x_40, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_ctor_set(x_26, 0, x_43);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
lean_ctor_set(x_34, 0, x_45);
lean_ctor_set(x_41, 0, x_34);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
lean_ctor_set(x_26, 0, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_26);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
lean_ctor_set(x_34, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_40);
lean_free_object(x_34);
lean_free_object(x_26);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
lean_dec(x_34);
x_56 = lean_nat_sub(x_36, x_55);
lean_dec(x_55);
lean_dec(x_36);
x_57 = l_Lean_mkNatLit(x_56);
lean_inc(x_57);
x_58 = l_Lean_Meta_mkEqRefl(x_57, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
lean_ctor_set(x_26, 0, x_59);
x_62 = 1;
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_26);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_57);
lean_free_object(x_26);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_26);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_dec(x_25);
x_71 = lean_ctor_get(x_23, 0);
lean_inc(x_71);
lean_dec(x_23);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
lean_dec(x_34);
x_75 = lean_nat_sub(x_71, x_74);
lean_dec(x_74);
lean_dec(x_71);
x_76 = l_Lean_mkNatLit(x_75);
lean_inc(x_72);
x_77 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_76, x_72);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_mk(x_81);
x_83 = l_Nat_reduceSubDiff___lambda__1___closed__2;
x_84 = l_Nat_applySimprocConst(x_77, x_83, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_82);
return x_84;
}
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_26, 0);
lean_inc(x_85);
lean_dec(x_26);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_12);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
lean_dec(x_25);
x_87 = lean_ctor_get(x_23, 0);
lean_inc(x_87);
lean_dec(x_23);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_nat_sub(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
x_91 = l_Lean_mkNatLit(x_90);
lean_inc(x_91);
x_92 = l_Lean_Meta_mkEqRefl(x_91, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_93);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_97);
if (lean_is_scalar(x_89)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_89;
}
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_95)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_95;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_94);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_91);
lean_dec(x_89);
x_101 = lean_ctor_get(x_92, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
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
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_105 = lean_ctor_get(x_25, 1);
lean_inc(x_105);
lean_dec(x_25);
x_106 = lean_ctor_get(x_23, 0);
lean_inc(x_106);
lean_dec(x_23);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_85, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_85, 2);
lean_inc(x_109);
lean_dec(x_85);
x_110 = lean_nat_sub(x_106, x_109);
lean_dec(x_109);
lean_dec(x_106);
x_111 = l_Lean_mkNatLit(x_110);
lean_inc(x_107);
x_112 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_111, x_107);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_12);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_mk(x_116);
x_118 = l_Nat_reduceSubDiff___lambda__1___closed__2;
x_119 = l_Nat_applySimprocConst(x_112, x_118, x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_105);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_12);
x_120 = lean_ctor_get(x_26, 0);
lean_inc(x_120);
lean_dec(x_26);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_25, 1);
lean_inc(x_121);
lean_dec(x_25);
x_122 = lean_ctor_get(x_23, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_23, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_23, 2);
lean_inc(x_124);
lean_dec(x_23);
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_nat_dec_le(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_nat_sub(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
x_128 = l_Lean_mkNatLit(x_127);
lean_inc(x_122);
x_129 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_122, x_128);
lean_inc(x_123);
lean_inc(x_24);
x_130 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_24, x_123);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_131 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_130, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_122);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_24);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_123);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_mk(x_138);
x_140 = l_Nat_reduceSubDiff___lambda__1___closed__4;
x_141 = l_Nat_applySimprocConst(x_129, x_140, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_139);
return x_141;
}
else
{
uint8_t x_142; 
lean_dec(x_129);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_142 = !lean_is_exclusive(x_131);
if (x_142 == 0)
{
return x_131;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_131, 0);
x_144 = lean_ctor_get(x_131, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_131);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; lean_object* x_147; 
x_146 = lean_nat_dec_eq(x_124, x_125);
lean_inc(x_24);
lean_inc(x_123);
x_147 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_123, x_24);
if (x_146 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_nat_sub(x_125, x_124);
lean_dec(x_124);
lean_dec(x_125);
x_149 = l_Lean_mkNatLit(x_148);
lean_inc(x_122);
x_150 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_122, x_149);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_151 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_147, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_24);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_123);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_122);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_mk(x_158);
x_160 = l_Nat_reduceSubDiff___lambda__1___closed__6;
x_161 = l_Nat_applySimprocConst(x_150, x_160, x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_153);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_159);
return x_161;
}
else
{
uint8_t x_162; 
lean_dec(x_150);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_162 = !lean_is_exclusive(x_151);
if (x_162 == 0)
{
return x_151;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_151, 0);
x_164 = lean_ctor_get(x_151, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_151);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_125);
lean_dec(x_124);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_166 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_147, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_24);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_123);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_122);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_122);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_array_mk(x_173);
x_175 = l_Nat_reduceSubDiff___lambda__1___closed__6;
x_176 = l_Nat_applySimprocConst(x_122, x_175, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_168);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_174);
return x_176;
}
else
{
uint8_t x_177; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_177 = !lean_is_exclusive(x_166);
if (x_177 == 0)
{
return x_166;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_166, 0);
x_179 = lean_ctor_get(x_166, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_166);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_24);
x_181 = lean_ctor_get(x_25, 1);
lean_inc(x_181);
lean_dec(x_25);
x_182 = lean_ctor_get(x_23, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_23, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_23, 2);
lean_inc(x_184);
lean_dec(x_23);
x_185 = lean_ctor_get(x_120, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 2);
lean_inc(x_187);
lean_dec(x_120);
x_188 = lean_nat_dec_le(x_184, x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_nat_sub(x_184, x_187);
lean_dec(x_187);
lean_dec(x_184);
x_190 = l_Lean_mkNatLit(x_189);
lean_inc(x_182);
x_191 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_182, x_190);
lean_inc(x_185);
x_192 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_191, x_185);
lean_inc(x_183);
lean_inc(x_186);
x_193 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_186, x_183);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_194 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_193, x_6, x_7, x_8, x_9, x_181);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_186);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_183);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_185);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_182);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_array_mk(x_202);
x_204 = l_Nat_reduceSubDiff___lambda__1___closed__8;
x_205 = l_Nat_applySimprocConst(x_192, x_204, x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_203);
return x_205;
}
else
{
uint8_t x_206; 
lean_dec(x_192);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_206 = !lean_is_exclusive(x_194);
if (x_206 == 0)
{
return x_194;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_194, 0);
x_208 = lean_ctor_get(x_194, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_194);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; lean_object* x_211; 
x_210 = lean_nat_dec_eq(x_184, x_187);
lean_inc(x_186);
lean_inc(x_183);
x_211 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(x_183, x_186);
if (x_210 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_nat_sub(x_187, x_184);
lean_dec(x_184);
lean_dec(x_187);
x_213 = l_Lean_mkNatLit(x_212);
lean_inc(x_185);
x_214 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(x_185, x_213);
lean_inc(x_182);
x_215 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_182, x_214);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_216 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_211, x_6, x_7, x_8, x_9, x_181);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_186);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_183);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_185);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_182);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_array_mk(x_224);
x_226 = l_Nat_reduceSubDiff___lambda__1___closed__10;
x_227 = l_Nat_applySimprocConst(x_215, x_226, x_225, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_218);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_225);
return x_227;
}
else
{
uint8_t x_228; 
lean_dec(x_215);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_228 = !lean_is_exclusive(x_216);
if (x_228 == 0)
{
return x_216;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_216, 0);
x_230 = lean_ctor_get(x_216, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_216);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_187);
lean_dec(x_184);
lean_inc(x_185);
lean_inc(x_182);
x_232 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(x_182, x_185);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_233 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(x_211, x_6, x_7, x_8, x_9, x_181);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_186);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_183);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_185);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_182);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_mk(x_241);
x_243 = l_Nat_reduceSubDiff___lambda__1___closed__10;
x_244 = l_Nat_applySimprocConst(x_232, x_243, x_242, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_235);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_242);
return x_244;
}
else
{
uint8_t x_245; 
lean_dec(x_232);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_245 = !lean_is_exclusive(x_233);
if (x_245 == 0)
{
return x_233;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_233, 0);
x_247 = lean_ctor_get(x_233, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_233);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
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
uint8_t x_249; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_249 = !lean_is_exclusive(x_25);
if (x_249 == 0)
{
return x_25;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_25, 0);
x_251 = lean_ctor_get(x_25, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_25);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_253 = !lean_is_exclusive(x_14);
if (x_253 == 0)
{
return x_14;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_14, 0);
x_255 = lean_ctor_get(x_14, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_14);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Nat_reduceBinPred___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Nat_reduceSubDiff___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_reduceSubDiff___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_reduceSubDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceSubDiff", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_reduceSucc___closed__1;
x_2 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2;
x_3 = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5;
x_4 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3;
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2;
x_3 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1;
x_3 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2;
x_4 = 1;
x_5 = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_reduceUnary___lambda__1___closed__1 = _init_l_Nat_reduceUnary___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceUnary___lambda__1___closed__1);
l_Nat_reduceBinPred___lambda__1___closed__1 = _init_l_Nat_reduceBinPred___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceBinPred___lambda__1___closed__1);
l_Nat_reduceBoolPred___lambda__1___closed__1 = _init_l_Nat_reduceBoolPred___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__1);
l_Nat_reduceBoolPred___lambda__1___closed__2 = _init_l_Nat_reduceBoolPred___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__2);
l_Nat_reduceBoolPred___lambda__1___closed__3 = _init_l_Nat_reduceBoolPred___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__3);
l_Nat_reduceBoolPred___lambda__1___closed__4 = _init_l_Nat_reduceBoolPred___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__4);
l_Nat_reduceBoolPred___lambda__1___closed__5 = _init_l_Nat_reduceBoolPred___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__5);
l_Nat_reduceBoolPred___lambda__1___closed__6 = _init_l_Nat_reduceBoolPred___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__6);
l_Nat_reduceBoolPred___lambda__1___closed__7 = _init_l_Nat_reduceBoolPred___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__7);
l_Nat_reduceBoolPred___lambda__1___closed__8 = _init_l_Nat_reduceBoolPred___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__8);
l_Nat_reduceBoolPred___lambda__1___closed__9 = _init_l_Nat_reduceBoolPred___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceBoolPred___lambda__1___closed__9);
l_Nat_reduceSucc___closed__1 = _init_l_Nat_reduceSucc___closed__1();
lean_mark_persistent(l_Nat_reduceSucc___closed__1);
l_Nat_reduceSucc___closed__2 = _init_l_Nat_reduceSucc___closed__2();
lean_mark_persistent(l_Nat_reduceSucc___closed__2);
l_Nat_reduceSucc___closed__3 = _init_l_Nat_reduceSucc___closed__3();
lean_mark_persistent(l_Nat_reduceSucc___closed__3);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__1);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__2);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__3);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__4);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__5);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__6);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_559_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__1);
l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561____closed__2);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_561_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1 = _init_l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceSucc_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_563_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceAdd___closed__1 = _init_l_Nat_reduceAdd___closed__1();
lean_mark_persistent(l_Nat_reduceAdd___closed__1);
l_Nat_reduceAdd___closed__2 = _init_l_Nat_reduceAdd___closed__2();
lean_mark_persistent(l_Nat_reduceAdd___closed__2);
l_Nat_reduceAdd___closed__3 = _init_l_Nat_reduceAdd___closed__3();
lean_mark_persistent(l_Nat_reduceAdd___closed__3);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__1);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__2);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__3);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__4);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__5);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__6);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__7);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__8);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__9);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__10);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__11);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__12);
l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597____closed__13);
if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_597_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1 = _init_l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_599_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAdd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_601_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMul___closed__1 = _init_l_Nat_reduceMul___closed__1();
lean_mark_persistent(l_Nat_reduceMul___closed__1);
l_Nat_reduceMul___closed__2 = _init_l_Nat_reduceMul___closed__2();
lean_mark_persistent(l_Nat_reduceMul___closed__2);
l_Nat_reduceMul___closed__3 = _init_l_Nat_reduceMul___closed__3();
lean_mark_persistent(l_Nat_reduceMul___closed__3);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__1);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__2);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__3);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__4);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__5);
l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_635_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1 = _init_l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_637_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMul_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_639_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceSub___closed__1 = _init_l_Nat_reduceSub___closed__1();
lean_mark_persistent(l_Nat_reduceSub___closed__1);
l_Nat_reduceSub___closed__2 = _init_l_Nat_reduceSub___closed__2();
lean_mark_persistent(l_Nat_reduceSub___closed__2);
l_Nat_reduceSub___closed__3 = _init_l_Nat_reduceSub___closed__3();
lean_mark_persistent(l_Nat_reduceSub___closed__3);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__1);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__2);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__3);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__4);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__5);
l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_673_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1 = _init_l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_675_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSub_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_677_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceDiv___closed__1 = _init_l_Nat_reduceDiv___closed__1();
lean_mark_persistent(l_Nat_reduceDiv___closed__1);
l_Nat_reduceDiv___closed__2 = _init_l_Nat_reduceDiv___closed__2();
lean_mark_persistent(l_Nat_reduceDiv___closed__2);
l_Nat_reduceDiv___closed__3 = _init_l_Nat_reduceDiv___closed__3();
lean_mark_persistent(l_Nat_reduceDiv___closed__3);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__1);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__2);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__3);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__4);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__5);
l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_711_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1 = _init_l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceDiv_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_715_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceMod___closed__1 = _init_l_Nat_reduceMod___closed__1();
lean_mark_persistent(l_Nat_reduceMod___closed__1);
l_Nat_reduceMod___closed__2 = _init_l_Nat_reduceMod___closed__2();
lean_mark_persistent(l_Nat_reduceMod___closed__2);
l_Nat_reduceMod___closed__3 = _init_l_Nat_reduceMod___closed__3();
lean_mark_persistent(l_Nat_reduceMod___closed__3);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__1);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__2);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__3);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__4);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__5);
l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_749_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1 = _init_l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_751_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceMod_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_753_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reducePow___closed__1 = _init_l_Nat_reducePow___closed__1();
lean_mark_persistent(l_Nat_reducePow___closed__1);
l_Nat_reducePow___closed__2 = _init_l_Nat_reducePow___closed__2();
lean_mark_persistent(l_Nat_reducePow___closed__2);
l_Nat_reducePow___closed__3 = _init_l_Nat_reducePow___closed__3();
lean_mark_persistent(l_Nat_reducePow___closed__3);
l_Nat_reducePow___closed__4 = _init_l_Nat_reducePow___closed__4();
lean_mark_persistent(l_Nat_reducePow___closed__4);
l_Nat_reducePow___closed__5 = _init_l_Nat_reducePow___closed__5();
lean_mark_persistent(l_Nat_reducePow___closed__5);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__1);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__2);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__3);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__4);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__5);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__6);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__7);
l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170____closed__8);
if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1170_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1 = _init_l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1172_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reducePow_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1174_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceAnd___closed__1 = _init_l_Nat_reduceAnd___closed__1();
lean_mark_persistent(l_Nat_reduceAnd___closed__1);
l_Nat_reduceAnd___closed__2 = _init_l_Nat_reduceAnd___closed__2();
lean_mark_persistent(l_Nat_reduceAnd___closed__2);
l_Nat_reduceAnd___closed__3 = _init_l_Nat_reduceAnd___closed__3();
lean_mark_persistent(l_Nat_reduceAnd___closed__3);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__1);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__2);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__3);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__4);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__5);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__6);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__7);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__8);
l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208____closed__9);
if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1208_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1 = _init_l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceAnd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1212_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceXor___closed__1 = _init_l_Nat_reduceXor___closed__1();
lean_mark_persistent(l_Nat_reduceXor___closed__1);
l_Nat_reduceXor___closed__2 = _init_l_Nat_reduceXor___closed__2();
lean_mark_persistent(l_Nat_reduceXor___closed__2);
l_Nat_reduceXor___closed__3 = _init_l_Nat_reduceXor___closed__3();
lean_mark_persistent(l_Nat_reduceXor___closed__3);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__1);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__2);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__3);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__4);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__5);
l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1246_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1 = _init_l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1248_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceXor_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1250_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__1);
l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__2);
l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__3);
l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__4);
l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__5);
l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1284_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1 = _init_l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1286_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceOr_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1288_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceShiftLeft___closed__1 = _init_l_Nat_reduceShiftLeft___closed__1();
lean_mark_persistent(l_Nat_reduceShiftLeft___closed__1);
l_Nat_reduceShiftLeft___closed__2 = _init_l_Nat_reduceShiftLeft___closed__2();
lean_mark_persistent(l_Nat_reduceShiftLeft___closed__2);
l_Nat_reduceShiftLeft___closed__3 = _init_l_Nat_reduceShiftLeft___closed__3();
lean_mark_persistent(l_Nat_reduceShiftLeft___closed__3);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__1);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__2);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__3);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__4);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__5);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__6);
l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322____closed__7);
if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1322_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1 = _init_l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1324_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftLeft_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1326_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceShiftRight___closed__1 = _init_l_Nat_reduceShiftRight___closed__1();
lean_mark_persistent(l_Nat_reduceShiftRight___closed__1);
l_Nat_reduceShiftRight___closed__2 = _init_l_Nat_reduceShiftRight___closed__2();
lean_mark_persistent(l_Nat_reduceShiftRight___closed__2);
l_Nat_reduceShiftRight___closed__3 = _init_l_Nat_reduceShiftRight___closed__3();
lean_mark_persistent(l_Nat_reduceShiftRight___closed__3);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__1);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__2);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__3);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__4);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__5);
l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1360_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1 = _init_l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1362_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceShiftRight_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1364_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGcd___closed__1 = _init_l_Nat_reduceGcd___closed__1();
lean_mark_persistent(l_Nat_reduceGcd___closed__1);
l_Nat_reduceGcd___closed__2 = _init_l_Nat_reduceGcd___closed__2();
lean_mark_persistent(l_Nat_reduceGcd___closed__2);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__1);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__2);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__3);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__4);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__5);
l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1382_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1 = _init_l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1384_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGcd_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1386_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLT___closed__1 = _init_l_Nat_reduceLT___closed__1();
lean_mark_persistent(l_Nat_reduceLT___closed__1);
l_Nat_reduceLT___closed__2 = _init_l_Nat_reduceLT___closed__2();
lean_mark_persistent(l_Nat_reduceLT___closed__2);
l_Nat_reduceLT___closed__3 = _init_l_Nat_reduceLT___closed__3();
lean_mark_persistent(l_Nat_reduceLT___closed__3);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__1);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__2);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__3);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__4);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__5);
l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1421_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1 = _init_l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1423_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1425_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceGT___closed__1 = _init_l_Nat_reduceGT___closed__1();
lean_mark_persistent(l_Nat_reduceGT___closed__1);
l_Nat_reduceGT___closed__2 = _init_l_Nat_reduceGT___closed__2();
lean_mark_persistent(l_Nat_reduceGT___closed__2);
l_Nat_reduceGT___closed__3 = _init_l_Nat_reduceGT___closed__3();
lean_mark_persistent(l_Nat_reduceGT___closed__3);
l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1 = _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__1);
l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2 = _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__2);
l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3 = _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1 = _init_l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1462_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1464_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceBEq___closed__1 = _init_l_Nat_reduceBEq___closed__1();
lean_mark_persistent(l_Nat_reduceBEq___closed__1);
l_Nat_reduceBEq___closed__2 = _init_l_Nat_reduceBEq___closed__2();
lean_mark_persistent(l_Nat_reduceBEq___closed__2);
l_Nat_reduceBEq___closed__3 = _init_l_Nat_reduceBEq___closed__3();
lean_mark_persistent(l_Nat_reduceBEq___closed__3);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__1);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__2);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__3);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__4);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__5);
l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1499_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1 = _init_l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1501_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1503_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceBNe___closed__1 = _init_l_Nat_reduceBNe___closed__1();
lean_mark_persistent(l_Nat_reduceBNe___closed__1);
l_Nat_reduceBNe___closed__2 = _init_l_Nat_reduceBNe___closed__2();
lean_mark_persistent(l_Nat_reduceBNe___closed__2);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__1);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__2);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__3);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__4);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__5);
l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1537_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1 = _init_l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1539_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1541_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_isValue___closed__1 = _init_l_Nat_isValue___closed__1();
lean_mark_persistent(l_Nat_isValue___closed__1);
l_Nat_isValue___closed__2 = _init_l_Nat_isValue___closed__2();
lean_mark_persistent(l_Nat_isValue___closed__2);
l_Nat_isValue___closed__3 = _init_l_Nat_isValue___closed__3();
lean_mark_persistent(l_Nat_isValue___closed__3);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__1);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__2);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__3);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__4);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__5);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__6);
l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713____closed__7);
if (builtin) {res = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1 = _init_l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715____closed__1);
if (builtin) {res = l___regBuiltin_Nat_isValue_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_1715_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__10);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__11);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__8);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__9);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__10);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__3);
l_Nat_reduceNatEqExpr___closed__1 = _init_l_Nat_reduceNatEqExpr___closed__1();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__1);
l_Nat_reduceNatEqExpr___closed__2 = _init_l_Nat_reduceNatEqExpr___closed__2();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__2);
l_Nat_reduceNatEqExpr___closed__3 = _init_l_Nat_reduceNatEqExpr___closed__3();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__3);
l_Nat_reduceNatEqExpr___closed__4 = _init_l_Nat_reduceNatEqExpr___closed__4();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__4);
l_Nat_reduceNatEqExpr___closed__5 = _init_l_Nat_reduceNatEqExpr___closed__5();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__5);
l_Nat_reduceNatEqExpr___closed__6 = _init_l_Nat_reduceNatEqExpr___closed__6();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__6);
l_Nat_reduceNatEqExpr___closed__7 = _init_l_Nat_reduceNatEqExpr___closed__7();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__7);
l_Nat_reduceNatEqExpr___closed__8 = _init_l_Nat_reduceNatEqExpr___closed__8();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__8);
l_Nat_reduceNatEqExpr___closed__9 = _init_l_Nat_reduceNatEqExpr___closed__9();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__9);
l_Nat_reduceNatEqExpr___closed__10 = _init_l_Nat_reduceNatEqExpr___closed__10();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__10);
l_Nat_reduceNatEqExpr___closed__11 = _init_l_Nat_reduceNatEqExpr___closed__11();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__11);
l_Nat_reduceNatEqExpr___closed__12 = _init_l_Nat_reduceNatEqExpr___closed__12();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__12);
l_Nat_reduceNatEqExpr___closed__13 = _init_l_Nat_reduceNatEqExpr___closed__13();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__13);
l_Nat_reduceNatEqExpr___closed__14 = _init_l_Nat_reduceNatEqExpr___closed__14();
lean_mark_persistent(l_Nat_reduceNatEqExpr___closed__14);
l_Nat_reduceEqDiff___lambda__1___closed__1 = _init_l_Nat_reduceEqDiff___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__1);
l_Nat_reduceEqDiff___lambda__1___closed__2 = _init_l_Nat_reduceEqDiff___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__2);
l_Nat_reduceEqDiff___lambda__1___closed__3 = _init_l_Nat_reduceEqDiff___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__3);
l_Nat_reduceEqDiff___lambda__1___closed__4 = _init_l_Nat_reduceEqDiff___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__4);
l_Nat_reduceEqDiff___lambda__1___closed__5 = _init_l_Nat_reduceEqDiff___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__5);
l_Nat_reduceEqDiff___lambda__1___closed__6 = _init_l_Nat_reduceEqDiff___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__6);
l_Nat_reduceEqDiff___lambda__1___closed__7 = _init_l_Nat_reduceEqDiff___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__7);
l_Nat_reduceEqDiff___lambda__1___closed__8 = _init_l_Nat_reduceEqDiff___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__8);
l_Nat_reduceEqDiff___lambda__1___closed__9 = _init_l_Nat_reduceEqDiff___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__9);
l_Nat_reduceEqDiff___lambda__1___closed__10 = _init_l_Nat_reduceEqDiff___lambda__1___closed__10();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__10);
l_Nat_reduceEqDiff___lambda__1___closed__11 = _init_l_Nat_reduceEqDiff___lambda__1___closed__11();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__11);
l_Nat_reduceEqDiff___lambda__1___closed__12 = _init_l_Nat_reduceEqDiff___lambda__1___closed__12();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__12);
l_Nat_reduceEqDiff___lambda__1___closed__13 = _init_l_Nat_reduceEqDiff___lambda__1___closed__13();
lean_mark_persistent(l_Nat_reduceEqDiff___lambda__1___closed__13);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__1);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__2);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__3);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__4);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__5);
l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3864_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1 = _init_l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3866_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceEqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_3868_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceBeqDiff___lambda__1___closed__1 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__1);
l_Nat_reduceBeqDiff___lambda__1___closed__2 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__2);
l_Nat_reduceBeqDiff___lambda__1___closed__3 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__3);
l_Nat_reduceBeqDiff___lambda__1___closed__4 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__4);
l_Nat_reduceBeqDiff___lambda__1___closed__5 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__5);
l_Nat_reduceBeqDiff___lambda__1___closed__6 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__6);
l_Nat_reduceBeqDiff___lambda__1___closed__7 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__7);
l_Nat_reduceBeqDiff___lambda__1___closed__8 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__8);
l_Nat_reduceBeqDiff___lambda__1___closed__9 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__9);
l_Nat_reduceBeqDiff___lambda__1___closed__10 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__10();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__10);
l_Nat_reduceBeqDiff___lambda__1___closed__11 = _init_l_Nat_reduceBeqDiff___lambda__1___closed__11();
lean_mark_persistent(l_Nat_reduceBeqDiff___lambda__1___closed__11);
l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1 = _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__1);
l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2 = _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__2);
l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3 = _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4101_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1 = _init_l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4103_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBeqDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4105_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceBneDiff___lambda__1___closed__1 = _init_l_Nat_reduceBneDiff___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__1);
l_Nat_reduceBneDiff___lambda__1___closed__2 = _init_l_Nat_reduceBneDiff___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__2);
l_Nat_reduceBneDiff___lambda__1___closed__3 = _init_l_Nat_reduceBneDiff___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__3);
l_Nat_reduceBneDiff___lambda__1___closed__4 = _init_l_Nat_reduceBneDiff___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__4);
l_Nat_reduceBneDiff___lambda__1___closed__5 = _init_l_Nat_reduceBneDiff___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__5);
l_Nat_reduceBneDiff___lambda__1___closed__6 = _init_l_Nat_reduceBneDiff___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__6);
l_Nat_reduceBneDiff___lambda__1___closed__7 = _init_l_Nat_reduceBneDiff___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceBneDiff___lambda__1___closed__7);
l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1 = _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__1);
l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2 = _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__2);
l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3 = _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4342_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1 = _init_l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4344_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceBneDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4346_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceLTLE___lambda__1___closed__1 = _init_l_Nat_reduceLTLE___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__1);
l_Nat_reduceLTLE___lambda__1___closed__2 = _init_l_Nat_reduceLTLE___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__2);
l_Nat_reduceLTLE___lambda__1___closed__3 = _init_l_Nat_reduceLTLE___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__3);
l_Nat_reduceLTLE___lambda__1___closed__4 = _init_l_Nat_reduceLTLE___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__4);
l_Nat_reduceLTLE___lambda__1___closed__5 = _init_l_Nat_reduceLTLE___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__5);
l_Nat_reduceLTLE___lambda__1___closed__6 = _init_l_Nat_reduceLTLE___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__6);
l_Nat_reduceLTLE___lambda__1___closed__7 = _init_l_Nat_reduceLTLE___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__7);
l_Nat_reduceLTLE___lambda__1___closed__8 = _init_l_Nat_reduceLTLE___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__8);
l_Nat_reduceLTLE___lambda__1___closed__9 = _init_l_Nat_reduceLTLE___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__9);
l_Nat_reduceLTLE___lambda__1___closed__10 = _init_l_Nat_reduceLTLE___lambda__1___closed__10();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__10);
l_Nat_reduceLTLE___lambda__1___closed__11 = _init_l_Nat_reduceLTLE___lambda__1___closed__11();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__11);
l_Nat_reduceLTLE___lambda__1___closed__12 = _init_l_Nat_reduceLTLE___lambda__1___closed__12();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__12);
l_Nat_reduceLTLE___lambda__1___closed__13 = _init_l_Nat_reduceLTLE___lambda__1___closed__13();
lean_mark_persistent(l_Nat_reduceLTLE___lambda__1___closed__13);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__1);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__2);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__3);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__4);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__5);
l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970____closed__6);
if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4970_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1 = _init_l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4972_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceLeDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_4974_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Nat_reduceSubDiff___lambda__1___closed__1 = _init_l_Nat_reduceSubDiff___lambda__1___closed__1();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__1);
l_Nat_reduceSubDiff___lambda__1___closed__2 = _init_l_Nat_reduceSubDiff___lambda__1___closed__2();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__2);
l_Nat_reduceSubDiff___lambda__1___closed__3 = _init_l_Nat_reduceSubDiff___lambda__1___closed__3();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__3);
l_Nat_reduceSubDiff___lambda__1___closed__4 = _init_l_Nat_reduceSubDiff___lambda__1___closed__4();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__4);
l_Nat_reduceSubDiff___lambda__1___closed__5 = _init_l_Nat_reduceSubDiff___lambda__1___closed__5();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__5);
l_Nat_reduceSubDiff___lambda__1___closed__6 = _init_l_Nat_reduceSubDiff___lambda__1___closed__6();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__6);
l_Nat_reduceSubDiff___lambda__1___closed__7 = _init_l_Nat_reduceSubDiff___lambda__1___closed__7();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__7);
l_Nat_reduceSubDiff___lambda__1___closed__8 = _init_l_Nat_reduceSubDiff___lambda__1___closed__8();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__8);
l_Nat_reduceSubDiff___lambda__1___closed__9 = _init_l_Nat_reduceSubDiff___lambda__1___closed__9();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__9);
l_Nat_reduceSubDiff___lambda__1___closed__10 = _init_l_Nat_reduceSubDiff___lambda__1___closed__10();
lean_mark_persistent(l_Nat_reduceSubDiff___lambda__1___closed__10);
l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1 = _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__1);
l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2 = _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2();
lean_mark_persistent(l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__2);
l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3 = _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3();
lean_mark_persistent(l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560____closed__3);
if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5560_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1 = _init_l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1();
lean_mark_persistent(l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562____closed__1);
if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5562_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Nat_reduceSubDiff_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat___hyg_5564_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
