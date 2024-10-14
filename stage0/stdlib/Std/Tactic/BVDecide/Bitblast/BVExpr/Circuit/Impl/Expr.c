// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.SignExtend Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object*, uint8_t);
lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkXorCached___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3;
lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkOrCached___rarg(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkBEqCached___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_instHashableBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorRefMkNotCached___rarg(lean_object*, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_11);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_2, x_4, x_5, x_1, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = 0;
x_8 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_10, x_4, x_5, x_6, x_11, x_13, lean_box(0), x_12);
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
x_17 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_15, x_4, x_5, x_6, x_16, x_18, lean_box(0), x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_9 = l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_2, x_3, x_1, x_2, x_8, x_4, lean_box(0), x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
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
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_11, x_15);
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
x_22 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_17, x_21);
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
x_30 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_29);
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
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_31, x_35);
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
x_42 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_37, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = 1;
lean_inc(x_1);
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_3);
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
x_10 = l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_5, x_6, x_9, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkBEqCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2;
x_5 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4;
x_11 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3;
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
x_13 = l_Std_Sat_AIG_RefVec_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_8, x_1);
x_10 = lean_array_push(x_7, x_6);
x_11 = l_Array_append___rarg(x_10, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_9);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_3);
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
x_15 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_16, x_1);
x_18 = lean_array_push(x_15, x_14);
x_19 = l_Array_append___rarg(x_18, x_13);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_20);
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
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorRefMkNotCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2;
x_5 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_1, x_2, x_6);
return x_7;
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
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_11, x_9);
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
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_13, x_15);
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
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_7, x_3);
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
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_13, x_15);
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
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_2, x_13);
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
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_7, x_9);
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
x_17 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(x_15, x_16);
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
x_24 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_21, x_23);
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
x_32 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(x_30, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_2, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_9);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 0, x_9);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_19, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 0, x_9);
x_25 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_23, x_21);
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
x_37 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_34, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_31);
x_41 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_38, x_40);
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
x_48 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_45, x_47);
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
x_60 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_57, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_20);
lean_ctor_set(x_63, 2, x_54);
x_64 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_61, x_63);
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
x_71 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_68, x_70);
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
x_76 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_72, x_75);
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
x_88 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_85, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_82);
x_92 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_89, x_91);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_22 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_17, x_15, x_4, x_5, x_6, x_7, x_18, x_19, x_20, x_21);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_11, x_13);
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
x_20 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_15, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc_n(x_8, 2);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_21, x_1, x_12, x_16, x_18, x_19, x_1, x_4, x_8, x_8);
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
x_27 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_24, x_26);
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
x_31 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_15, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc_n(x_8, 2);
lean_inc(x_1);
x_34 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_32, x_1, x_12, x_16, x_28, x_29, x_1, x_4, x_8, x_8);
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
x_38 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_35, x_37);
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
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_11, x_13);
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
x_20 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_15, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_21, x_1, x_12, x_16, x_18, x_19, x_1, x_4, x_8, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 0, x_22);
x_27 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_25, x_23);
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
x_31 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_28, x_30);
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
x_35 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_15, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_1);
x_38 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_36, x_1, x_12, x_16, x_32, x_33, x_1, x_4, x_8, x_8);
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
x_43 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_39, x_42);
lean_dec(x_1);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_4, x_5, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_12 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(x_2, x_4, x_5, x_6, x_8, lean_box(0), x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_6, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
x_13 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_14 = lean_array_fget(x_4, x_12);
lean_dec(x_12);
x_15 = lean_array_push(x_8, x_14);
x_3 = lean_box(0);
x_6 = x_13;
x_7 = lean_box(0);
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
x_19 = lean_array_fget(x_4, x_6);
lean_dec(x_6);
x_20 = lean_array_push(x_8, x_19);
x_3 = lean_box(0);
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_free_object(x_3);
x_9 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(x_2, x_5, lean_box(0), x_6, x_1, x_7, lean_box(0), x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(x_2, x_13, lean_box(0), x_14, x_1, x_15, lean_box(0), x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_2, x_12);
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
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(x_1, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(x_1, x_4, x_11, x_6, x_7, x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_2, x_12);
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
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(x_1, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(x_1, x_4, x_11, x_6, x_7, x_12);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkOrCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkXorCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20), 2, 0);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_8, x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_10, 0, x_8);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_12, x_10);
lean_dec(x_10);
lean_dec(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_14, x_16);
lean_dec(x_16);
lean_dec(x_1);
return x_17;
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 3);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_18);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_18, x_2, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
x_25 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_22, x_24);
lean_dec(x_24);
lean_dec(x_1);
return x_25;
}
case 4:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_1);
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_30, x_28);
switch (x_27) {
case 0:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_35 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4;
x_36 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3;
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_34, x_37);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4;
x_43 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3;
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_39, x_44);
lean_dec(x_1);
return x_45;
}
}
case 1:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_48 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_47, x_50);
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_31);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_56 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_52, x_57);
lean_dec(x_1);
return x_58;
}
}
case 2:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_61 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_62 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_32);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_60, x_63);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_69 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
x_71 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_65, x_70);
lean_dec(x_1);
return x_71;
}
}
case 3:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_32);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_74 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_73, x_32);
lean_dec(x_32);
lean_dec(x_1);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_32, 0);
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_32);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_75, x_77);
lean_dec(x_77);
lean_dec(x_1);
return x_78;
}
}
case 4:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_32);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_81 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_80, x_32);
lean_dec(x_1);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_32, 0);
x_83 = lean_ctor_get(x_32, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_32);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_31);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_82, x_84);
lean_dec(x_1);
return x_85;
}
}
case 5:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_32);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_88 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(x_1, x_87, x_32);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_32, 0);
x_90 = lean_ctor_get(x_32, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_32);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_31);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(x_1, x_89, x_91);
return x_92;
}
}
default: 
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_32, 0, x_31);
x_95 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_94, x_32);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_32, 0);
x_97 = lean_ctor_get(x_32, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_32);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_31);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_96, x_98);
return x_99;
}
}
}
}
case 5:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_3, 2);
lean_inc(x_101);
lean_dec(x_3);
lean_inc(x_1);
x_102 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_101);
switch (lean_obj_tag(x_100)) {
case 0:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_103, x_104);
lean_dec(x_1);
return x_105;
}
case 1:
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
lean_dec(x_100);
lean_ctor_set(x_102, 1, x_109);
lean_ctor_set(x_102, 0, x_108);
x_110 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_107, x_102);
lean_dec(x_102);
lean_dec(x_1);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_102, 0);
x_112 = lean_ctor_get(x_102, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_102);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
lean_dec(x_100);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_111, x_114);
lean_dec(x_114);
lean_dec(x_1);
return x_115;
}
}
case 2:
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_102);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_102, 0);
x_118 = lean_ctor_get(x_102, 1);
x_119 = lean_ctor_get(x_100, 0);
lean_inc(x_119);
lean_dec(x_100);
lean_ctor_set(x_102, 1, x_119);
lean_ctor_set(x_102, 0, x_118);
x_120 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_117, x_102);
lean_dec(x_102);
lean_dec(x_1);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_102, 0);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_102);
x_123 = lean_ctor_get(x_100, 0);
lean_inc(x_123);
lean_dec(x_100);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_121, x_124);
lean_dec(x_124);
lean_dec(x_1);
return x_125;
}
}
case 3:
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_102);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_102, 0);
x_128 = lean_ctor_get(x_102, 1);
x_129 = lean_ctor_get(x_100, 0);
lean_inc(x_129);
lean_dec(x_100);
lean_ctor_set(x_102, 1, x_129);
lean_ctor_set(x_102, 0, x_128);
x_130 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_127, x_102);
lean_dec(x_1);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_102, 0);
x_132 = lean_ctor_get(x_102, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_102);
x_133 = lean_ctor_get(x_100, 0);
lean_inc(x_133);
lean_dec(x_100);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_131, x_134);
lean_dec(x_1);
return x_135;
}
}
case 4:
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_102);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_102, 0);
x_138 = lean_ctor_get(x_102, 1);
x_139 = lean_ctor_get(x_100, 0);
lean_inc(x_139);
lean_dec(x_100);
lean_ctor_set(x_102, 1, x_139);
lean_ctor_set(x_102, 0, x_138);
x_140 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_137, x_102);
lean_dec(x_1);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_102, 0);
x_142 = lean_ctor_get(x_102, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_102);
x_143 = lean_ctor_get(x_100, 0);
lean_inc(x_143);
lean_dec(x_100);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_141, x_144);
lean_dec(x_1);
return x_145;
}
}
default: 
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_102);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_102, 0);
x_148 = lean_ctor_get(x_102, 1);
x_149 = lean_ctor_get(x_100, 0);
lean_inc(x_149);
lean_dec(x_100);
lean_ctor_set(x_102, 1, x_149);
lean_ctor_set(x_102, 0, x_148);
x_150 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_1, x_147, x_102);
lean_dec(x_1);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_102, 0);
x_152 = lean_ctor_get(x_102, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_102);
x_153 = lean_ctor_get(x_100, 0);
lean_inc(x_153);
lean_dec(x_100);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_1, x_151, x_154);
lean_dec(x_1);
return x_155;
}
}
}
}
case 6:
{
uint8_t x_156; 
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_3);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_157 = lean_ctor_get(x_3, 0);
x_158 = lean_ctor_get(x_3, 1);
x_159 = lean_ctor_get(x_3, 2);
x_160 = lean_ctor_get(x_3, 3);
lean_inc(x_157);
x_161 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_157, x_2, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_158);
x_164 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_158, x_162, x_160);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_nat_add(x_157, x_158);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 3, x_166);
lean_ctor_set(x_3, 2, x_163);
x_168 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(x_167, x_165, x_3);
lean_dec(x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_169 = lean_ctor_get(x_3, 0);
x_170 = lean_ctor_get(x_3, 1);
x_171 = lean_ctor_get(x_3, 2);
x_172 = lean_ctor_get(x_3, 3);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_3);
lean_inc(x_169);
x_173 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_169, x_2, x_171);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_170);
x_176 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_170, x_174, x_172);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_nat_add(x_169, x_170);
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_169);
lean_ctor_set(x_180, 1, x_170);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_178);
x_181 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(x_179, x_177, x_180);
lean_dec(x_179);
return x_181;
}
}
case 7:
{
uint8_t x_182; 
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_3);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_3, 0);
x_184 = lean_ctor_get(x_3, 1);
x_185 = lean_ctor_get(x_3, 2);
lean_inc(x_183);
x_186 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_183, x_2, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_nat_mul(x_183, x_184);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 2, x_188);
x_190 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(x_189, x_187, x_3);
lean_dec(x_3);
lean_dec(x_189);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_3, 0);
x_192 = lean_ctor_get(x_3, 1);
x_193 = lean_ctor_get(x_3, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_194 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_191, x_2, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_nat_mul(x_191, x_192);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 2, x_196);
x_199 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(x_197, x_195, x_198);
lean_dec(x_198);
lean_dec(x_197);
return x_199;
}
}
case 8:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_3, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_3, 2);
lean_inc(x_201);
lean_dec(x_3);
lean_inc(x_200);
x_202 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_200, x_2, x_201);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
lean_ctor_set(x_202, 0, x_200);
x_205 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(x_1, x_204, x_202);
lean_dec(x_1);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_202, 0);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_202);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_200);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(x_1, x_206, x_208);
lean_dec(x_1);
return x_209;
}
}
case 9:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_3, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_3, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_3, 3);
lean_inc(x_212);
lean_dec(x_3);
lean_inc(x_1);
x_213 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_210);
x_216 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_210, x_214, x_212);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set(x_219, 1, x_215);
lean_ctor_set(x_219, 2, x_218);
x_220 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(x_1, x_217, x_219);
lean_dec(x_1);
return x_220;
}
default: 
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_221 = lean_ctor_get(x_3, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_3, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_3, 3);
lean_inc(x_223);
lean_dec(x_3);
lean_inc(x_1);
x_224 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_222);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
lean_inc(x_221);
x_227 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_221, x_225, x_223);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_226);
lean_ctor_set(x_230, 2, x_229);
x_231 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(x_1, x_228, x_230);
lean_dec(x_1);
return x_231;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Sat_AIG_RefVec_fold_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__30(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__32(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__33(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__36(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__35(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__38(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__39(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__37(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__41(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__42(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__40(x_1, x_2, x_3);
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
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_go), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2;
return x_1;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_SignExtend(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin, lean_io_mk_world());
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
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_SignExtend(builtin, lean_io_mk_world());
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
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__1);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__2);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__3);
l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4 = _init_l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___closed__4);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4);
l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1);
l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2);
l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast = _init_l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
