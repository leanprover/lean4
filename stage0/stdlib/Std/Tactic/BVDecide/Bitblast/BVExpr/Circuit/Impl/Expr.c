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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkXorCached___rarg(lean_object*, lean_object*);
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_instHashableBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__2(x_2, x_4, x_5, x_1, x_6, lean_box(0), x_7);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = 0;
x_9 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_nat_dec_le(x_7, x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_7, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_16 = lean_array_push(x_15, x_12);
lean_ctor_set(x_9, 1, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_17 = lean_array_fget(x_5, x_7);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_19 = lean_array_push(x_18, x_17);
lean_ctor_set(x_9, 1, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_22 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_11, x_4, x_5, x_7, x_12, x_20, lean_box(0), x_21);
lean_ctor_set(x_9, 1, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_nat_dec_le(x_7, x_6);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_7, x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_28 = lean_array_push(x_27, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_30 = lean_array_fget(x_5, x_7);
x_31 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_32 = lean_array_push(x_31, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_36 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__4(x_1, x_23, x_4, x_5, x_7, x_24, x_34, lean_box(0), x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
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
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
lean_inc(x_2);
x_9 = l_Std_Sat_AIG_RefVec_zip_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__6(x_1, x_2, x_3, x_1, x_2, x_7, x_8, lean_box(0), x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
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
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
lean_inc(x_2);
x_7 = l_Std_Sat_AIG_RefVec_map_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_1, x_2, x_3, x_1, x_2, x_5, lean_box(0), x_6, x_4);
lean_dec(x_4);
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__11(x_1, x_2, x_4, x_5, x_6, lean_box(0), x_7);
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
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_5, x_6, x_7, lean_box(0), x_8);
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
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__13(x_1, x_2, x_10, x_11, x_12, lean_box(0), x_13);
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
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_5, x_6, x_7, lean_box(0), x_8);
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
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__15(x_1, x_2, x_10, x_11, x_12, lean_box(0), x_13);
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
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_5, x_6, x_7, lean_box(0), x_8);
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
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__17(x_1, x_2, x_10, x_11, x_12, lean_box(0), x_13);
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
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_2, x_4, x_5, x_6, x_7, lean_box(0), x_8);
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
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
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
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1;
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
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(x_1, x_2, x_6);
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
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
lean_inc(x_19);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_19, x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_sub(x_20, x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 3, x_21);
lean_ctor_set(x_3, 2, x_20);
lean_ctor_set(x_3, 1, x_25);
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_28, x_24, x_3);
lean_dec(x_3);
lean_dec(x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_34 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_30, x_2, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_sub(x_31, x_32);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_32);
x_41 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__3(x_39, x_35, x_40);
lean_dec(x_40);
lean_dec(x_39);
return x_41;
}
}
case 4:
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
lean_dec(x_3);
lean_inc(x_1);
x_45 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_1);
x_48 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_46, x_44);
switch (x_43) {
case 0:
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
x_51 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_52 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_50, x_53);
lean_dec(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__2;
x_59 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__1;
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_55, x_60);
lean_dec(x_1);
return x_61;
}
}
case 1:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
x_64 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_65 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_63, x_66);
lean_dec(x_1);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_48, 0);
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_48);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__4;
x_72 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__3;
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_72);
x_74 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_68, x_73);
lean_dec(x_1);
return x_74;
}
}
case 2:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_48);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
x_77 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6;
x_78 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5;
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_48);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_76, x_79);
lean_dec(x_1);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_47);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__6;
x_85 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go___closed__5;
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = l_Std_Sat_AIG_RefVec_zip___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__5(x_1, x_81, x_86);
lean_dec(x_1);
return x_87;
}
}
case 3:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_48);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
x_90 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_89, x_48);
lean_dec(x_48);
lean_dec(x_1);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_48, 0);
x_92 = lean_ctor_get(x_48, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_48);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_47);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_91, x_93);
lean_dec(x_93);
lean_dec(x_1);
return x_94;
}
}
default: 
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_48);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
x_97 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_96, x_48);
lean_dec(x_1);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_48, 0);
x_99 = lean_ctor_get(x_48, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_48);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_47);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_98, x_100);
lean_dec(x_1);
return x_101;
}
}
}
}
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_3, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_3, 2);
lean_inc(x_103);
lean_dec(x_3);
lean_inc(x_1);
x_104 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_103);
switch (lean_obj_tag(x_102)) {
case 0:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__7(x_1, x_105, x_106);
lean_dec(x_1);
return x_107;
}
case 1:
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = lean_ctor_get(x_104, 1);
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
lean_dec(x_102);
lean_ctor_set(x_104, 1, x_111);
lean_ctor_set(x_104, 0, x_110);
x_112 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_109, x_104);
lean_dec(x_104);
lean_dec(x_1);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_104, 0);
x_114 = lean_ctor_get(x_104, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_104);
x_115 = lean_ctor_get(x_102, 0);
lean_inc(x_115);
lean_dec(x_102);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_113, x_116);
lean_dec(x_116);
lean_dec(x_1);
return x_117;
}
}
case 2:
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_104);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_104, 0);
x_120 = lean_ctor_get(x_104, 1);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
lean_dec(x_102);
lean_ctor_set(x_104, 1, x_121);
lean_ctor_set(x_104, 0, x_120);
x_122 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_119, x_104);
lean_dec(x_104);
lean_dec(x_1);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_104, 0);
x_124 = lean_ctor_get(x_104, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_104);
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
lean_dec(x_102);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__10(x_1, x_123, x_126);
lean_dec(x_126);
lean_dec(x_1);
return x_127;
}
}
case 3:
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_104);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_104, 0);
x_130 = lean_ctor_get(x_104, 1);
x_131 = lean_ctor_get(x_102, 0);
lean_inc(x_131);
lean_dec(x_102);
lean_ctor_set(x_104, 1, x_131);
lean_ctor_set(x_104, 0, x_130);
x_132 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_129, x_104);
lean_dec(x_1);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_104, 0);
x_134 = lean_ctor_get(x_104, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_104);
x_135 = lean_ctor_get(x_102, 0);
lean_inc(x_135);
lean_dec(x_102);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__12(x_1, x_133, x_136);
lean_dec(x_1);
return x_137;
}
}
case 4:
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_104);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_104, 0);
x_140 = lean_ctor_get(x_104, 1);
x_141 = lean_ctor_get(x_102, 0);
lean_inc(x_141);
lean_dec(x_102);
lean_ctor_set(x_104, 1, x_141);
lean_ctor_set(x_104, 0, x_140);
x_142 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_139, x_104);
lean_dec(x_1);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_104, 0);
x_144 = lean_ctor_get(x_104, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_104);
x_145 = lean_ctor_get(x_102, 0);
lean_inc(x_145);
lean_dec(x_102);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__14(x_1, x_143, x_146);
lean_dec(x_1);
return x_147;
}
}
default: 
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_104);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_104, 0);
x_150 = lean_ctor_get(x_104, 1);
x_151 = lean_ctor_get(x_102, 0);
lean_inc(x_151);
lean_dec(x_102);
lean_ctor_set(x_104, 1, x_151);
lean_ctor_set(x_104, 0, x_150);
x_152 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_149, x_104);
lean_dec(x_1);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_104, 0);
x_154 = lean_ctor_get(x_104, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_104);
x_155 = lean_ctor_get(x_102, 0);
lean_inc(x_155);
lean_dec(x_102);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__16(x_1, x_153, x_156);
lean_dec(x_1);
return x_157;
}
}
}
}
case 6:
{
uint8_t x_158; 
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_3);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_159 = lean_ctor_get(x_3, 0);
x_160 = lean_ctor_get(x_3, 1);
x_161 = lean_ctor_get(x_3, 2);
x_162 = lean_ctor_get(x_3, 3);
lean_inc(x_159);
x_163 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_159, x_2, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_160);
x_166 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_160, x_164, x_162);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_nat_add(x_159, x_160);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 3, x_168);
lean_ctor_set(x_3, 2, x_165);
x_170 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_169, x_167, x_3);
lean_dec(x_169);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_171 = lean_ctor_get(x_3, 0);
x_172 = lean_ctor_get(x_3, 1);
x_173 = lean_ctor_get(x_3, 2);
x_174 = lean_ctor_get(x_3, 3);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_3);
lean_inc(x_171);
x_175 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_171, x_2, x_173);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_172);
x_178 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_172, x_176, x_174);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_nat_add(x_171, x_172);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_171);
lean_ctor_set(x_182, 1, x_172);
lean_ctor_set(x_182, 2, x_177);
lean_ctor_set(x_182, 3, x_180);
x_183 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__18(x_181, x_179, x_182);
lean_dec(x_181);
return x_183;
}
}
case 7:
{
uint8_t x_184; 
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_3);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_ctor_get(x_3, 0);
x_186 = lean_ctor_get(x_3, 1);
x_187 = lean_ctor_get(x_3, 2);
lean_inc(x_185);
x_188 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_185, x_2, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_nat_mul(x_185, x_186);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 2, x_190);
x_192 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_191, x_189, x_3);
lean_dec(x_3);
lean_dec(x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = lean_ctor_get(x_3, 0);
x_194 = lean_ctor_get(x_3, 1);
x_195 = lean_ctor_get(x_3, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_3);
lean_inc(x_193);
x_196 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_193, x_2, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_nat_mul(x_193, x_194);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_193);
lean_ctor_set(x_200, 1, x_194);
lean_ctor_set(x_200, 2, x_198);
x_201 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__19(x_199, x_197, x_200);
lean_dec(x_200);
lean_dec(x_199);
return x_201;
}
}
case 8:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_ctor_get(x_3, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 2);
lean_inc(x_203);
lean_dec(x_3);
lean_inc(x_202);
x_204 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_202, x_2, x_203);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_ctor_set(x_204, 0, x_202);
x_207 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_1, x_206, x_204);
lean_dec(x_1);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_204, 0);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_204);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSignExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__21(x_1, x_208, x_210);
lean_dec(x_1);
return x_211;
}
}
case 9:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_212 = lean_ctor_get(x_3, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_3, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_3, 3);
lean_inc(x_214);
lean_dec(x_3);
lean_inc(x_1);
x_215 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_213);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_212);
x_218 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_212, x_216, x_214);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_212);
lean_ctor_set(x_221, 1, x_217);
lean_ctor_set(x_221, 2, x_220);
x_222 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__23(x_1, x_219, x_221);
lean_dec(x_1);
return x_222;
}
default: 
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_223 = lean_ctor_get(x_3, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_3, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_3, 3);
lean_inc(x_225);
lean_dec(x_3);
lean_inc(x_1);
x_226 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_1, x_2, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
lean_inc(x_223);
x_229 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_223, x_227, x_225);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set(x_232, 1, x_228);
lean_ctor_set(x_232, 2, x_231);
x_233 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__26(x_1, x_230, x_232);
lean_dec(x_1);
return x_233;
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
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__1___closed__1);
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
