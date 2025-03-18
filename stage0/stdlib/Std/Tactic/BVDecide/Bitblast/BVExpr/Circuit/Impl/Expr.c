// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
// Imports: Init.Data.AC Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_7, x_1);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_nat_add(x_5, x_7);
x_12 = lean_nat_dec_lt(x_11, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_inc(x_6);
x_15 = lean_array_push(x_9, x_6);
x_7 = x_14;
x_8 = lean_box(0);
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_4, x_11);
lean_dec(x_11);
x_18 = lean_array_push(x_9, x_17);
x_7 = x_14;
x_8 = lean_box(0);
x_9 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = 0;
x_8 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_1, x_10, x_4, x_5, x_6, x_11, x_13, lean_box(0), x_12);
lean_ctor_set(x_8, 1, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_1, x_15, x_4, x_5, x_6, x_16, x_18, lean_box(0), x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_lt(x_6, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
x_16 = lean_array_fget(x_9, x_6);
x_17 = lean_array_fget(x_10, x_6);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_apply_2(x_11, x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_push(x_7, x_21);
x_5 = x_20;
x_6 = x_15;
x_7 = x_22;
x_8 = lean_box(0);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_9 = l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_2, x_3, x_1, x_2, x_8, x_4, lean_box(0), x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = 1;
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
x_10 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_8);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_8);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = 0;
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = 1;
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_27);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_31, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_27);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_27);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_37, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_lt(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
x_13 = lean_array_fget(x_7, x_5);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_8, x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_3 = x_16;
x_4 = x_17;
x_5 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = 1;
lean_inc(x_1);
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_1, x_2, x_5, x_6, x_9, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_5, x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = 0;
x_12 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_array_push(x_7, x_14);
x_1 = x_13;
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
x_21 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_22 = lean_array_push(x_7, x_21);
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_2, x_4, x_5, x_1, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_8, x_1);
x_10 = lean_array_push(x_7, x_6);
x_11 = l_Array_append___rarg(x_10, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_9);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_3);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_16, x_1);
x_18 = lean_array_push(x_15, x_14);
x_19 = l_Array_append___rarg(x_18, x_13);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_20);
lean_dec(x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_nat_dec_lt(x_6, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_6, x_13);
x_15 = lean_array_fget(x_9, x_6);
lean_dec(x_6);
x_16 = lean_apply_2(x_10, x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_8, x_18);
x_5 = x_17;
x_6 = x_14;
x_7 = lean_box(0);
x_8 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_7 = l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_1, x_2, x_3, x_1, x_2, x_6, lean_box(0), x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_BitVec_ofNat(x_1, x_7);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_5, x_8);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_9, 0, x_6);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_11, x_9);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_13, x_15);
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_8);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_7, x_3);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_13, x_15);
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_5, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
x_11 = lean_array_fget(x_3, x_5);
x_12 = lean_array_fget(x_4, x_5);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_6);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(x_2, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_2 = x_15;
x_5 = x_10;
x_6 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(x_4, x_1, x_6, x_7, x_8, x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_8);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_21, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_26);
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_25, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_30, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
x_13 = lean_nat_add(x_8, x_11);
x_14 = lean_nat_dec_lt(x_12, x_1);
if (x_14 == 0)
{
lean_inc(x_3);
x_15 = x_3;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_array_fget(x_5, x_12);
x_15 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_2, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_9);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 0, x_9);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_19, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 0, x_9);
x_25 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_23, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_6);
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_26, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_6);
lean_inc(x_1);
x_33 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_1, x_30, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_27);
x_37 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_34, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_31);
x_41 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_38, x_40);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_12);
lean_ctor_set(x_44, 2, x_13);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_4);
x_48 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_45, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_6);
lean_inc(x_20);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_6);
x_52 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_49, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_20);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_20);
lean_ctor_set(x_55, 1, x_6);
lean_inc(x_1);
x_56 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_1, x_53, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_58);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_50);
x_60 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_57, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_20);
lean_ctor_set(x_63, 2, x_54);
x_64 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_61, x_63);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_12);
lean_ctor_set(x_67, 2, x_13);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set(x_67, 4, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_68 = lean_ctor_get(x_17, 0);
x_69 = lean_ctor_get(x_17, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_17);
lean_inc(x_9);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_3);
x_71 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_68, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_4);
x_76 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_72, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_6);
lean_inc(x_69);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_6);
x_80 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_77, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_69);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_69);
lean_ctor_set(x_83, 1, x_6);
lean_inc(x_1);
x_84 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_1, x_81, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_86);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_73);
lean_ctor_set(x_87, 2, x_78);
x_88 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_85, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_82);
x_92 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_89, x_91);
lean_dec(x_1);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_12);
lean_ctor_set(x_95, 2, x_13);
lean_ctor_set(x_95, 3, x_90);
lean_ctor_set(x_95, 4, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_17, x_15, x_4, x_5, x_6, x_7, x_18, x_19, x_20, x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_11);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_BitVec_ofNat(x_1, x_4);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_2, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 0;
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_19);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_19);
lean_inc(x_1);
x_20 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_15, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc_n(x_8, 2);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_21, x_1, x_12, x_16, x_18, x_19, x_1, x_4, x_8, x_8);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_8);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_24, x_26);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
lean_inc(x_1);
x_31 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_15, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc_n(x_8, 2);
lean_inc(x_1);
x_34 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_32, x_1, x_12, x_16, x_28, x_29, x_1, x_4, x_8, x_8);
lean_dec(x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_35, x_37);
lean_dec(x_1);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_BitVec_ofNat(x_1, x_4);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_2, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 0;
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_19);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_19);
lean_inc(x_1);
x_20 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_15, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_21, x_1, x_12, x_16, x_18, x_19, x_1, x_4, x_8, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 0, x_22);
x_27 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_25, x_23);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_28, x_30);
lean_dec(x_1);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
lean_inc(x_1);
x_35 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_15, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_1);
x_38 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_36, x_1, x_12, x_16, x_32, x_33, x_1, x_4, x_8, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 3, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_40);
x_43 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_39, x_42);
lean_dec(x_1);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_mod(x_4, x_1);
x_10 = lean_nat_dec_lt(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_sub(x_5, x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_11);
lean_dec(x_11);
x_15 = lean_array_push(x_7, x_14);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_nat_sub(x_1, x_9);
lean_dec(x_9);
x_18 = lean_nat_add(x_17, x_5);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_array_fget(x_3, x_18);
lean_dec(x_18);
x_22 = lean_array_push(x_7, x_21);
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_nat_mod(x_4, x_1);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_nat_dec_lt(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_12 = lean_nat_sub(x_5, x_10);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_array_fget(x_3, x_12);
lean_dec(x_12);
x_16 = lean_array_push(x_7, x_15);
x_5 = x_14;
x_6 = lean_box(0);
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_18 = lean_nat_add(x_9, x_5);
lean_dec(x_9);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_array_fget(x_3, x_18);
lean_dec(x_18);
x_22 = lean_array_push(x_7, x_21);
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_add(x_4, x_5);
x_10 = lean_nat_dec_lt(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_1, x_11);
x_13 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_12);
lean_dec(x_12);
x_15 = lean_array_push(x_7, x_14);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = lean_array_fget(x_3, x_9);
lean_dec(x_9);
x_20 = lean_array_push(x_7, x_19);
x_5 = x_18;
x_6 = lean_box(0);
x_7 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Array_append___rarg(x_5, x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_3);
if (x_8 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_11 = l_Array_append___rarg(x_7, x_4);
x_5 = x_10;
x_6 = lean_box(0);
x_7 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(x_2, x_4, x_5, x_6, x_8, lean_box(0), x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_nat_dec_lt(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_pow(x_10, x_7);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_1, x_2, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_fget(x_6, x_7);
lean_inc(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_5);
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(x_1, x_3, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_14;
x_5 = x_11;
x_6 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(x_1, x_4, x_11, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_nat_add(x_4, x_5);
x_11 = lean_nat_dec_lt(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_12 = 0;
x_13 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_push(x_7, x_15);
x_2 = x_14;
x_5 = x_17;
x_6 = lean_box(0);
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_22 = lean_array_fget(x_3, x_10);
lean_dec(x_10);
x_23 = lean_array_push(x_7, x_22);
x_5 = x_21;
x_6 = lean_box(0);
x_7 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(x_1, x_2, x_4, x_5, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_nat_dec_lt(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_pow(x_10, x_7);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(x_1, x_2, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_fget(x_6, x_7);
lean_inc(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_5);
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(x_1, x_3, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_14;
x_5 = x_11;
x_6 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(x_1, x_4, x_11, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_nat_dec_lt(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_pow(x_10, x_7);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_fget(x_6, x_7);
lean_inc(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_5);
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_11);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(x_1, x_3, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_14;
x_5 = x_11;
x_6 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43(x_1, x_4, x_11, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(x_1, x_2, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_2, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_8);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_8, x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_12, x_14);
lean_dec(x_14);
lean_dec(x_1);
return x_15;
}
case 3:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_1);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_21, x_18);
switch (x_17) {
case 0:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_26 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2;
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_23);
x_27 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_25, x_19);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2;
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_19, 0, x_30);
x_32 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_28, x_19);
lean_dec(x_1);
return x_32;
}
}
case 1:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_23);
x_36 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_34, x_19);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_39);
x_41 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_37, x_19);
lean_dec(x_1);
return x_41;
}
}
case 2:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_44 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
lean_ctor_set(x_19, 1, x_44);
lean_ctor_set(x_19, 0, x_23);
x_45 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_43, x_19);
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
lean_ctor_set(x_19, 1, x_49);
lean_ctor_set(x_19, 0, x_48);
x_50 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_46, x_19);
lean_dec(x_1);
return x_50;
}
}
case 3:
{
uint8_t x_51; 
lean_free_object(x_19);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_53 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_52, x_23);
lean_dec(x_23);
lean_dec(x_1);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_22);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_54, x_56);
lean_dec(x_56);
lean_dec(x_1);
return x_57;
}
}
case 4:
{
uint8_t x_58; 
lean_free_object(x_19);
x_58 = !lean_is_exclusive(x_23);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_60 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_59, x_23);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_22);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_61, x_63);
lean_dec(x_1);
return x_64;
}
}
case 5:
{
uint8_t x_65; 
lean_free_object(x_19);
x_65 = !lean_is_exclusive(x_23);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_67 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_66, x_23);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_23, 0);
x_69 = lean_ctor_get(x_23, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_23);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_22);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_68, x_70);
return x_71;
}
}
default: 
{
uint8_t x_72; 
lean_free_object(x_19);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
x_74 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_73, x_23);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_23, 0);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_23);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_22);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_75, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_19, 0);
x_80 = lean_ctor_get(x_19, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_19);
lean_inc(x_1);
x_81 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_79, x_18);
switch (x_17) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_82, x_87);
lean_dec(x_1);
return x_88;
}
case 1:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_89, x_94);
lean_dec(x_1);
return x_95;
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_98 = x_81;
} else {
 lean_dec_ref(x_81);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_80);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_96, x_101);
lean_dec(x_1);
return x_102;
}
case 3:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_81, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_80);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_103, x_106);
lean_dec(x_106);
lean_dec(x_1);
return x_107;
}
case 4:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_81, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_110 = x_81;
} else {
 lean_dec_ref(x_81);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_80);
lean_ctor_set(x_111, 1, x_109);
x_112 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_108, x_111);
lean_dec(x_1);
return x_112;
}
case 5:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_81, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_81, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_115 = x_81;
} else {
 lean_dec_ref(x_81);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_80);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_113, x_116);
return x_117;
}
default: 
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_81, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_81, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_120 = x_81;
} else {
 lean_dec_ref(x_81);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_80);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_118, x_121);
return x_122;
}
}
}
}
case 4:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_3, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 2);
lean_inc(x_124);
lean_dec(x_3);
lean_inc(x_1);
x_125 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_124);
switch (lean_obj_tag(x_123)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_126, x_127);
lean_dec(x_1);
return x_128;
}
case 1:
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
x_132 = lean_ctor_get(x_123, 0);
lean_inc(x_132);
lean_dec(x_123);
lean_ctor_set(x_125, 1, x_132);
lean_ctor_set(x_125, 0, x_131);
x_133 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_130, x_125);
lean_dec(x_1);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_125, 0);
x_135 = lean_ctor_get(x_125, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_125);
x_136 = lean_ctor_get(x_123, 0);
lean_inc(x_136);
lean_dec(x_123);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_134, x_137);
lean_dec(x_1);
return x_138;
}
}
case 2:
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_125);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_125, 0);
x_141 = lean_ctor_get(x_125, 1);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
lean_dec(x_123);
lean_ctor_set(x_125, 1, x_142);
lean_ctor_set(x_125, 0, x_141);
x_143 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_140, x_125);
lean_dec(x_1);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_125, 0);
x_145 = lean_ctor_get(x_125, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_125);
x_146 = lean_ctor_get(x_123, 0);
lean_inc(x_146);
lean_dec(x_123);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_144, x_147);
lean_dec(x_1);
return x_148;
}
}
default: 
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_125);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_125, 0);
x_151 = lean_ctor_get(x_125, 1);
x_152 = lean_ctor_get(x_123, 0);
lean_inc(x_152);
lean_dec(x_123);
lean_ctor_set(x_125, 1, x_152);
lean_ctor_set(x_125, 0, x_151);
x_153 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_150, x_125);
lean_dec(x_1);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_125, 0);
x_155 = lean_ctor_get(x_125, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_125);
x_156 = lean_ctor_get(x_123, 0);
lean_inc(x_156);
lean_dec(x_123);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_154, x_157);
lean_dec(x_1);
return x_158;
}
}
}
}
case 5:
{
uint8_t x_159; 
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_3);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_160 = lean_ctor_get(x_3, 0);
x_161 = lean_ctor_get(x_3, 1);
x_162 = lean_ctor_get(x_3, 2);
x_163 = lean_ctor_get(x_3, 3);
lean_inc(x_160);
x_164 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_160, x_2, x_162);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_161);
x_167 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_161, x_165, x_163);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_nat_add(x_160, x_161);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 3, x_169);
lean_ctor_set(x_3, 2, x_166);
x_171 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_170, x_168, x_3);
lean_dec(x_170);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_172 = lean_ctor_get(x_3, 0);
x_173 = lean_ctor_get(x_3, 1);
x_174 = lean_ctor_get(x_3, 2);
x_175 = lean_ctor_get(x_3, 3);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_3);
lean_inc(x_172);
x_176 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_172, x_2, x_174);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_173);
x_179 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_173, x_177, x_175);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_nat_add(x_172, x_173);
x_183 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_183, 0, x_172);
lean_ctor_set(x_183, 1, x_173);
lean_ctor_set(x_183, 2, x_178);
lean_ctor_set(x_183, 3, x_181);
x_184 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_182, x_180, x_183);
lean_dec(x_182);
return x_184;
}
}
case 6:
{
uint8_t x_185; 
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_3);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = lean_ctor_get(x_3, 0);
x_187 = lean_ctor_get(x_3, 1);
x_188 = lean_ctor_get(x_3, 2);
lean_inc(x_186);
x_189 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_186, x_2, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_nat_mul(x_186, x_187);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 2, x_191);
x_193 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_192, x_190, x_3);
lean_dec(x_3);
lean_dec(x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_3, 0);
x_195 = lean_ctor_get(x_3, 1);
x_196 = lean_ctor_get(x_3, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_3);
lean_inc(x_194);
x_197 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_194, x_2, x_196);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_nat_mul(x_194, x_195);
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_195);
lean_ctor_set(x_201, 2, x_199);
x_202 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_200, x_198, x_201);
lean_dec(x_201);
lean_dec(x_200);
return x_202;
}
}
case 7:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_203 = lean_ctor_get(x_3, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_3, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_3, 3);
lean_inc(x_205);
lean_dec(x_3);
lean_inc(x_1);
x_206 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_203);
x_209 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_203, x_207, x_205);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_212, 0, x_203);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_212, 2, x_211);
x_213 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(x_1, x_210, x_212);
lean_dec(x_1);
return x_213;
}
case 8:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_3, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_3, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_3, 3);
lean_inc(x_216);
lean_dec(x_3);
lean_inc(x_1);
x_217 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_215);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_214);
x_220 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_214, x_218, x_216);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_214);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_222);
x_224 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(x_1, x_221, x_223);
lean_dec(x_1);
return x_224;
}
default: 
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_225 = lean_ctor_get(x_3, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_3, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_3, 3);
lean_inc(x_227);
lean_dec(x_3);
lean_inc(x_1);
x_228 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_226);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_225);
x_231 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_225, x_229, x_227);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_234, 0, x_225);
lean_ctor_set(x_234, 1, x_230);
lean_ctor_set(x_234, 2, x_233);
x_235 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(x_1, x_232, x_234);
lean_dec(x_1);
return x_235;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__43(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__1);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
