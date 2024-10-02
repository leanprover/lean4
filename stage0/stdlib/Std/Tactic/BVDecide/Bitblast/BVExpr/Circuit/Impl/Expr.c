// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.SignExtend Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object*, uint8_t);
lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkXorCached___rarg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__2;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instLawfulVecOperatorBVBitBitblast;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5;
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkOrCached___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_instHashableBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_7 = l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_1, x_2, x_3, x_1, x_2, x_6, lean_box(0), x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorRefMkNotCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2;
x_5 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_4, x_5, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_5, x_6, x_8, lean_box(0), x_7);
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
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_10, x_11, x_13, lean_box(0), x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_2, x_4, x_5, x_6, x_8, lean_box(0), x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(x_2, x_5, lean_box(0), x_6, x_1, x_7, lean_box(0), x_9);
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
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(x_2, x_13, lean_box(0), x_14, x_1, x_15, lean_box(0), x_17);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_12);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_3, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_15;
x_5 = x_12;
x_6 = lean_box(0);
x_7 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_4, x_11, x_6, x_7, lean_box(0), x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_12);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_3, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_15;
x_5 = x_12;
x_6 = lean_box(0);
x_7 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_4, x_11, x_6, x_7, lean_box(0), x_12);
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
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkOrCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit;
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1;
x_3 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkXorCached___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6() {
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
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_36 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
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
x_42 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_43 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
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
x_48 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
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
x_55 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_56 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
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
x_61 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6;
x_62 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5;
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
x_68 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6;
x_69 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5;
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
default: 
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
}
}
case 5:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
lean_dec(x_3);
lean_inc(x_1);
x_88 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_87);
switch (lean_obj_tag(x_86)) {
case 0:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(x_1, x_89, x_90);
lean_dec(x_1);
return x_91;
}
case 1:
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
lean_dec(x_86);
lean_ctor_set(x_88, 1, x_95);
lean_ctor_set(x_88, 0, x_94);
x_96 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_93, x_88);
lean_dec(x_88);
lean_dec(x_1);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_ctor_get(x_86, 0);
lean_inc(x_99);
lean_dec(x_86);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_97, x_100);
lean_dec(x_100);
lean_dec(x_1);
return x_101;
}
}
case 2:
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_88);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_88, 0);
x_104 = lean_ctor_get(x_88, 1);
x_105 = lean_ctor_get(x_86, 0);
lean_inc(x_105);
lean_dec(x_86);
lean_ctor_set(x_88, 1, x_105);
lean_ctor_set(x_88, 0, x_104);
x_106 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_103, x_88);
lean_dec(x_88);
lean_dec(x_1);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_88, 0);
x_108 = lean_ctor_get(x_88, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_88);
x_109 = lean_ctor_get(x_86, 0);
lean_inc(x_109);
lean_dec(x_86);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_107, x_110);
lean_dec(x_110);
lean_dec(x_1);
return x_111;
}
}
case 3:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_88);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_88, 0);
x_114 = lean_ctor_get(x_88, 1);
x_115 = lean_ctor_get(x_86, 0);
lean_inc(x_115);
lean_dec(x_86);
lean_ctor_set(x_88, 1, x_115);
lean_ctor_set(x_88, 0, x_114);
x_116 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_113, x_88);
lean_dec(x_1);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_88, 0);
x_118 = lean_ctor_get(x_88, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_88);
x_119 = lean_ctor_get(x_86, 0);
lean_inc(x_119);
lean_dec(x_86);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_117, x_120);
lean_dec(x_1);
return x_121;
}
}
case 4:
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_88);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_88, 0);
x_124 = lean_ctor_get(x_88, 1);
x_125 = lean_ctor_get(x_86, 0);
lean_inc(x_125);
lean_dec(x_86);
lean_ctor_set(x_88, 1, x_125);
lean_ctor_set(x_88, 0, x_124);
x_126 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_123, x_88);
lean_dec(x_1);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_88, 0);
x_128 = lean_ctor_get(x_88, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_88);
x_129 = lean_ctor_get(x_86, 0);
lean_inc(x_129);
lean_dec(x_86);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_127, x_130);
lean_dec(x_1);
return x_131;
}
}
default: 
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_88);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_88, 0);
x_134 = lean_ctor_get(x_88, 1);
x_135 = lean_ctor_get(x_86, 0);
lean_inc(x_135);
lean_dec(x_86);
lean_ctor_set(x_88, 1, x_135);
lean_ctor_set(x_88, 0, x_134);
x_136 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_133, x_88);
lean_dec(x_1);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_88, 0);
x_138 = lean_ctor_get(x_88, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_88);
x_139 = lean_ctor_get(x_86, 0);
lean_inc(x_139);
lean_dec(x_86);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_137, x_140);
lean_dec(x_1);
return x_141;
}
}
}
}
case 6:
{
uint8_t x_142; 
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_3);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_143 = lean_ctor_get(x_3, 0);
x_144 = lean_ctor_get(x_3, 1);
x_145 = lean_ctor_get(x_3, 2);
x_146 = lean_ctor_get(x_3, 3);
lean_inc(x_143);
x_147 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_143, x_2, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_144);
x_150 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_144, x_148, x_146);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_nat_add(x_143, x_144);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 3, x_152);
lean_ctor_set(x_3, 2, x_149);
x_154 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_153, x_151, x_3);
lean_dec(x_153);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_3, 0);
x_156 = lean_ctor_get(x_3, 1);
x_157 = lean_ctor_get(x_3, 2);
x_158 = lean_ctor_get(x_3, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_3);
lean_inc(x_155);
x_159 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_155, x_2, x_157);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_156);
x_162 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_156, x_160, x_158);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_nat_add(x_155, x_156);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_156);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set(x_166, 3, x_164);
x_167 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_165, x_163, x_166);
lean_dec(x_165);
return x_167;
}
}
case 7:
{
uint8_t x_168; 
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_3);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_3, 0);
x_170 = lean_ctor_get(x_3, 1);
x_171 = lean_ctor_get(x_3, 2);
lean_inc(x_169);
x_172 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_169, x_2, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_nat_mul(x_169, x_170);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 2, x_174);
x_176 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_175, x_173, x_3);
lean_dec(x_3);
lean_dec(x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_ctor_get(x_3, 0);
x_178 = lean_ctor_get(x_3, 1);
x_179 = lean_ctor_get(x_3, 2);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_3);
lean_inc(x_177);
x_180 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_177, x_2, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_nat_mul(x_177, x_178);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_178);
lean_ctor_set(x_184, 2, x_182);
x_185 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_183, x_181, x_184);
lean_dec(x_184);
lean_dec(x_183);
return x_185;
}
}
case 8:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_3, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_3, 2);
lean_inc(x_187);
lean_dec(x_3);
lean_inc(x_186);
x_188 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_186, x_2, x_187);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_188, 0);
lean_ctor_set(x_188, 0, x_186);
x_191 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_1, x_190, x_188);
lean_dec(x_1);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_188, 0);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_188);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_186);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_1, x_192, x_194);
lean_dec(x_1);
return x_195;
}
}
case 9:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_196 = lean_ctor_get(x_3, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_3, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 3);
lean_inc(x_198);
lean_dec(x_3);
lean_inc(x_1);
x_199 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_197);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
lean_inc(x_196);
x_202 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_196, x_200, x_198);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_201);
lean_ctor_set(x_205, 2, x_204);
x_206 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_203, x_205);
lean_dec(x_1);
return x_206;
}
default: 
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_207 = lean_ctor_get(x_3, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_3, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_3, 3);
lean_inc(x_209);
lean_dec(x_3);
lean_inc(x_1);
x_210 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_208);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_207);
x_213 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_207, x_211, x_209);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_207);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_214, x_216);
lean_dec(x_1);
return x_217;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_map___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__24(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_2, x_3);
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
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5);
l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6);
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
