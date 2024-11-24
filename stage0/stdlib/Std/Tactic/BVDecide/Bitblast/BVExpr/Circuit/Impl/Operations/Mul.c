// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
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
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1;
static lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg___boxed(lean_object*, lean_object*);
uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
static uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object*);
static lean_object* _init_l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1;
return x_2;
}
}
static uint64_t _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 0;
x_2 = 13;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 0;
x_2 = 11;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 0)
{
uint64_t x_3; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1;
return x_3;
}
else
{
uint64_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2;
return x_4;
}
}
case 1:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 1;
x_7 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_13 = 2;
x_14 = lean_uint64_of_nat(x_9);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_uint64_of_nat(x_10);
x_17 = lean_uint64_mix_hash(x_15, x_16);
if (x_11 == 0)
{
uint64_t x_18; uint64_t x_19; 
x_18 = 13;
x_19 = lean_uint64_mix_hash(x_17, x_18);
if (x_12 == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_mix_hash(x_19, x_18);
return x_20;
}
else
{
uint64_t x_21; uint64_t x_22; 
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_19, x_21);
return x_22;
}
}
else
{
uint64_t x_23; uint64_t x_24; 
x_23 = 11;
x_24 = lean_uint64_mix_hash(x_17, x_23);
if (x_12 == 0)
{
uint64_t x_25; uint64_t x_26; 
x_25 = 13;
x_26 = lean_uint64_mix_hash(x_24, x_25);
return x_26;
}
else
{
uint64_t x_27; 
x_27 = lean_uint64_mix_hash(x_24, x_23);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 0);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, 0);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_25; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_25 = lean_nat_dec_eq(x_13, x_17);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_14, x_18);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
else
{
if (x_15 == 0)
{
if (x_19 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_21 = x_29;
goto block_24;
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
else
{
if (x_19 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_21 = x_32;
goto block_24;
}
}
}
}
block_24:
{
lean_dec(x_21);
if (x_16 == 0)
{
if (x_20 == 0)
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
return x_20;
}
}
}
else
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(x_2, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_array_get_size(x_7);
x_9 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_3, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_7, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(x_26);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_24);
return x_2;
}
else
{
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_24);
return x_2;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_box(0);
x_35 = lean_array_uset(x_7, x_20, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_3, x_4, x_21);
x_37 = lean_array_uset(x_35, x_20, x_36);
lean_ctor_set(x_2, 1, x_37);
return x_2;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = lean_array_get_size(x_39);
x_41 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_3);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_39, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_3, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_38, x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_53);
x_58 = lean_array_uset(x_39, x_52, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(x_58);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_39, x_52, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_3, x_4, x_53);
x_71 = lean_array_uset(x_69, x_52, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_38);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
static lean_object* _init_l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_6, 0, x_2);
x_7 = l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_4);
lean_inc(x_6);
x_9 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_6);
x_10 = lean_array_push(x_4, x_6);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_16, 0, x_2);
x_17 = l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_get_size(x_14);
lean_inc(x_16);
x_19 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_14, x_15, x_16);
x_20 = lean_array_push(x_14, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_sub(x_5, x_4);
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
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = 0;
x_18 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_23 = lean_array_push(x_7, x_20);
x_2 = x_19;
x_5 = x_22;
x_6 = lean_box(0);
x_7 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_1, x_2, x_4, x_5, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_inc(x_10);
lean_inc(x_7);
x_12 = lean_alloc_ctor(2, 2, 2);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*2 + 1, x_11);
x_20 = l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(x_5, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fget(x_4, x_7);
x_22 = lean_array_fget(x_4, x_10);
switch (lean_obj_tag(x_21)) {
case 0:
{
uint8_t x_23; 
lean_dec(x_6);
x_23 = lean_ctor_get_uint8(x_21, 0);
lean_dec(x_21);
if (x_23 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_22, 0);
lean_dec(x_22);
if (x_24 == 0)
{
if (x_8 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_5);
x_26 = 0;
x_27 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_25, x_26);
return x_27;
}
else
{
if (x_11 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_12);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
x_29 = 0;
x_30 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_28, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_array_get_size(x_4);
lean_inc(x_12);
x_32 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_33 = lean_array_push(x_4, x_12);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
lean_dec(x_12);
if (x_8 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
x_37 = 0;
x_38 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_36, x_37);
return x_38;
}
else
{
if (x_11 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_5);
lean_inc(x_10);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_5);
x_42 = 0;
x_43 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_41, x_42);
return x_43;
}
}
}
}
else
{
lean_dec(x_22);
if (x_8 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_12);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_45 = 0;
x_46 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_44, x_45);
return x_46;
}
else
{
if (x_11 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_12);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_5);
lean_inc(x_10);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_array_get_size(x_4);
lean_inc(x_12);
x_50 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_51 = lean_array_push(x_4, x_12);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_54; 
lean_dec(x_12);
x_54 = lean_ctor_get_uint8(x_22, 0);
lean_dec(x_22);
if (x_54 == 0)
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_5);
x_56 = 0;
x_57 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_55, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_5);
lean_inc(x_7);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_5);
x_61 = 0;
x_62 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_60, x_61);
return x_62;
}
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_5);
lean_inc(x_10);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_5);
x_66 = 0;
x_67 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_65, x_66);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = 0;
x_70 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_68, x_69);
return x_70;
}
}
}
else
{
lean_dec(x_22);
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_12);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_5);
lean_inc(x_10);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_10);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_eq(x_7, x_10);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_array_get_size(x_4);
lean_inc(x_12);
x_75 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_76 = lean_array_push(x_4, x_12);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; 
lean_dec(x_12);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = 0;
x_81 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_79, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
lean_dec(x_12);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_5);
x_83 = 0;
x_84 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_82, x_83);
return x_84;
}
}
}
}
case 1:
{
lean_dec(x_21);
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_85; 
lean_dec(x_6);
x_85 = lean_ctor_get_uint8(x_22, 0);
lean_dec(x_22);
if (x_85 == 0)
{
if (x_8 == 0)
{
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_4);
lean_ctor_set(x_86, 1, x_5);
x_87 = 0;
x_88 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_86, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_89, 1, x_5);
lean_inc(x_7);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_7);
return x_90;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
lean_dec(x_12);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_4);
lean_ctor_set(x_91, 1, x_5);
x_92 = 0;
x_93 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_91, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_array_get_size(x_4);
lean_inc(x_12);
x_95 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_96 = lean_array_push(x_4, x_12);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_4);
lean_ctor_set(x_99, 1, x_5);
lean_inc(x_7);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
return x_100;
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_4);
lean_ctor_set(x_101, 1, x_5);
x_102 = 0;
x_103 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_101, x_102);
return x_103;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_104; 
x_104 = lean_nat_dec_eq(x_7, x_10);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_array_get_size(x_4);
lean_inc(x_12);
x_106 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_107 = lean_array_push(x_4, x_12);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
else
{
lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_12);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_5);
x_111 = 0;
x_112 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_110, x_111);
return x_112;
}
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; 
lean_dec(x_12);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_5);
x_114 = 0;
x_115 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_113, x_114);
return x_115;
}
}
}
}
case 1:
{
uint8_t x_116; lean_object* x_117; 
lean_dec(x_22);
x_116 = lean_nat_dec_eq(x_7, x_10);
if (x_116 == 0)
{
lean_object* x_128; 
x_128 = lean_box(0);
x_117 = x_128;
goto block_127;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_12);
lean_dec(x_6);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_4);
lean_ctor_set(x_129, 1, x_5);
lean_inc(x_7);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
return x_130;
}
else
{
lean_object* x_131; 
x_131 = lean_box(0);
x_117 = x_131;
goto block_127;
}
}
else
{
lean_object* x_132; 
x_132 = lean_box(0);
x_117 = x_132;
goto block_127;
}
}
block_127:
{
lean_dec(x_117);
if (x_116 == 0)
{
lean_object* x_118; 
x_118 = lean_box(0);
x_13 = x_118;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_119; 
x_119 = lean_box(0);
x_13 = x_119;
goto block_19;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; 
lean_dec(x_12);
lean_dec(x_6);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_4);
lean_ctor_set(x_120, 1, x_5);
x_121 = 0;
x_122 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_120, x_121);
return x_122;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_123; uint8_t x_124; lean_object* x_125; 
lean_dec(x_12);
lean_dec(x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_4);
lean_ctor_set(x_123, 1, x_5);
x_124 = 0;
x_125 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_123, x_124);
return x_125;
}
else
{
lean_object* x_126; 
x_126 = lean_box(0);
x_13 = x_126;
goto block_19;
}
}
}
}
}
default: 
{
uint8_t x_133; lean_object* x_134; 
lean_dec(x_22);
x_133 = lean_nat_dec_eq(x_7, x_10);
if (x_133 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_134 = x_145;
goto block_144;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_12);
lean_dec(x_6);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_4);
lean_ctor_set(x_146, 1, x_5);
lean_inc(x_7);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_7);
return x_147;
}
else
{
lean_object* x_148; 
x_148 = lean_box(0);
x_134 = x_148;
goto block_144;
}
}
else
{
lean_object* x_149; 
x_149 = lean_box(0);
x_134 = x_149;
goto block_144;
}
}
block_144:
{
lean_dec(x_134);
if (x_133 == 0)
{
lean_object* x_135; 
x_135 = lean_box(0);
x_13 = x_135;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_13 = x_136;
goto block_19;
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; 
lean_dec(x_12);
lean_dec(x_6);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_5);
x_138 = 0;
x_139 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_137, x_138);
return x_139;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; 
lean_dec(x_12);
lean_dec(x_6);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_4);
lean_ctor_set(x_140, 1, x_5);
x_141 = 0;
x_142 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_140, x_141);
return x_142;
}
else
{
lean_object* x_143; 
x_143 = lean_box(0);
x_13 = x_143;
goto block_19;
}
}
}
}
}
}
}
default: 
{
lean_dec(x_21);
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_150; 
lean_dec(x_6);
x_150 = lean_ctor_get_uint8(x_22, 0);
lean_dec(x_22);
if (x_150 == 0)
{
if (x_8 == 0)
{
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_4);
lean_ctor_set(x_151, 1, x_5);
x_152 = 0;
x_153 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_151, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_4);
lean_ctor_set(x_154, 1, x_5);
lean_inc(x_7);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_7);
return x_155;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; 
lean_dec(x_12);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_4);
lean_ctor_set(x_156, 1, x_5);
x_157 = 0;
x_158 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_156, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_array_get_size(x_4);
lean_inc(x_12);
x_160 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_161 = lean_array_push(x_4, x_12);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_4);
lean_ctor_set(x_164, 1, x_5);
lean_inc(x_7);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_7);
return x_165;
}
else
{
lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_4);
lean_ctor_set(x_166, 1, x_5);
x_167 = 0;
x_168 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_166, x_167);
return x_168;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_eq(x_7, x_10);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_array_get_size(x_4);
lean_inc(x_12);
x_171 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_172 = lean_array_push(x_4, x_12);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
else
{
lean_object* x_175; uint8_t x_176; lean_object* x_177; 
lean_dec(x_12);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_4);
lean_ctor_set(x_175, 1, x_5);
x_176 = 0;
x_177 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_175, x_176);
return x_177;
}
}
else
{
lean_object* x_178; uint8_t x_179; lean_object* x_180; 
lean_dec(x_12);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_4);
lean_ctor_set(x_178, 1, x_5);
x_179 = 0;
x_180 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_178, x_179);
return x_180;
}
}
}
}
case 1:
{
uint8_t x_181; lean_object* x_182; 
lean_dec(x_22);
x_181 = lean_nat_dec_eq(x_7, x_10);
if (x_181 == 0)
{
lean_object* x_193; 
x_193 = lean_box(0);
x_182 = x_193;
goto block_192;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_12);
lean_dec(x_6);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_4);
lean_ctor_set(x_194, 1, x_5);
lean_inc(x_7);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_7);
return x_195;
}
else
{
lean_object* x_196; 
x_196 = lean_box(0);
x_182 = x_196;
goto block_192;
}
}
else
{
lean_object* x_197; 
x_197 = lean_box(0);
x_182 = x_197;
goto block_192;
}
}
block_192:
{
lean_dec(x_182);
if (x_181 == 0)
{
lean_object* x_183; 
x_183 = lean_box(0);
x_13 = x_183;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_184; 
x_184 = lean_box(0);
x_13 = x_184;
goto block_19;
}
else
{
lean_object* x_185; uint8_t x_186; lean_object* x_187; 
lean_dec(x_12);
lean_dec(x_6);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_4);
lean_ctor_set(x_185, 1, x_5);
x_186 = 0;
x_187 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_185, x_186);
return x_187;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_188; uint8_t x_189; lean_object* x_190; 
lean_dec(x_12);
lean_dec(x_6);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_4);
lean_ctor_set(x_188, 1, x_5);
x_189 = 0;
x_190 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_188, x_189);
return x_190;
}
else
{
lean_object* x_191; 
x_191 = lean_box(0);
x_13 = x_191;
goto block_19;
}
}
}
}
}
default: 
{
uint8_t x_198; lean_object* x_199; 
lean_dec(x_22);
x_198 = lean_nat_dec_eq(x_7, x_10);
if (x_198 == 0)
{
lean_object* x_210; 
x_210 = lean_box(0);
x_199 = x_210;
goto block_209;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_12);
lean_dec(x_6);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_4);
lean_ctor_set(x_211, 1, x_5);
lean_inc(x_7);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_7);
return x_212;
}
else
{
lean_object* x_213; 
x_213 = lean_box(0);
x_199 = x_213;
goto block_209;
}
}
else
{
lean_object* x_214; 
x_214 = lean_box(0);
x_199 = x_214;
goto block_209;
}
}
block_209:
{
lean_dec(x_199);
if (x_198 == 0)
{
lean_object* x_200; 
x_200 = lean_box(0);
x_13 = x_200;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_201; 
x_201 = lean_box(0);
x_13 = x_201;
goto block_19;
}
else
{
lean_object* x_202; uint8_t x_203; lean_object* x_204; 
lean_dec(x_12);
lean_dec(x_6);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_4);
lean_ctor_set(x_202, 1, x_5);
x_203 = 0;
x_204 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_202, x_203);
return x_204;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_205; uint8_t x_206; lean_object* x_207; 
lean_dec(x_12);
lean_dec(x_6);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_4);
lean_ctor_set(x_205, 1, x_5);
x_206 = 0;
x_207 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_205, x_206);
return x_207;
}
else
{
lean_object* x_208; 
x_208 = lean_box(0);
x_13 = x_208;
goto block_19;
}
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
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_12);
lean_dec(x_6);
x_215 = lean_ctor_get(x_20, 0);
lean_inc(x_215);
lean_dec(x_20);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_4);
lean_ctor_set(x_216, 1, x_5);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_4);
lean_inc(x_12);
x_15 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_16 = lean_array_push(x_4, x_12);
if (lean_is_scalar(x_6)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_6;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_5);
x_9 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1, x_2);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1, x_2);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
x_17 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_12);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_30, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_32);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_37, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 1;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_10, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_13, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_27, x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_22);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_30, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
x_15 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_13);
x_18 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_17, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_19, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg(x_4, x_2, lean_box(0));
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_4, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
x_13 = lean_array_fget(x_3, x_5);
x_14 = lean_array_fget(x_4, x_5);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_7);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_8, x_18);
x_2 = x_17;
x_5 = x_12;
x_6 = lean_box(0);
x_7 = x_19;
x_8 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = 0;
x_5 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(x_1, x_6, x_8, x_9, x_11, lean_box(0), x_7, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = 1;
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(x_8, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_11, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_9);
x_17 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_16, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_18, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
x_13 = lean_array_fget(x_6, x_3);
x_14 = lean_array_fget(x_7, x_3);
lean_dec(x_3);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_8, x_18);
x_2 = x_17;
x_3 = x_12;
x_4 = lean_box(0);
x_8 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(x_1, x_2, x_8, lean_box(0), x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_5, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_5);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_6);
lean_ctor_set(x_10, 0, x_6);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_12, x_10);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_fget(x_4, x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_6);
x_18 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_2 = x_19;
x_5 = x_22;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
lean_inc(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_24, x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_fget(x_4, x_5);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_6);
x_32 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_28, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_2 = x_33;
x_5 = x_36;
x_6 = x_34;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_399____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Cache_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Nat_testBit(x_3, x_4);
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = lean_array_push(x_5, x_12);
x_2 = x_11;
x_4 = x_14;
x_5 = x_15;
x_6 = lean_box(0);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2(x_1, x_2, x_3, x_5, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_BitVec_ofNat(x_1, x_4);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_2, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_array_fget(x_11, x_4);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_9);
x_14 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(x_1, x_15, x_10, x_11, x_17, x_16);
lean_dec(x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1;
x_14 = l_outOfBounds___rarg(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_3 = x_12;
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_14);
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_19; 
x_19 = lean_array_fget(x_8, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_3 = x_12;
x_5 = x_21;
goto _start;
}
else
{
lean_dec(x_19);
x_3 = x_12;
goto _start;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2(x_1, x_2, x_9, x_10, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(x_2, x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(x_2, x_6);
lean_dec(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_11);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(x_1, x_2, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(x_1, x_2, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1 = _init_l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___closed__1);
l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1 = _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1();
l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2 = _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_83____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2();
l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___closed__1 = _init_l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___closed__1);
l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
