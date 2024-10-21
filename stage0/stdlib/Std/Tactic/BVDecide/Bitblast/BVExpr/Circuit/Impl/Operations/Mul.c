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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_array_get_size(x_4);
x_22 = lean_array_fget(x_4, x_7);
x_23 = lean_array_fget(x_4, x_10);
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_24; 
lean_dec(x_6);
x_24 = lean_ctor_get_uint8(x_22, 0);
lean_dec(x_22);
if (x_24 == 0)
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_25 == 0)
{
if (x_8 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
x_27 = 0;
x_28 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_26, x_27);
return x_28;
}
else
{
if (x_11 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_5);
x_30 = 0;
x_31 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_12);
x_32 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_33 = lean_array_push(x_4, x_12);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_21);
return x_35;
}
}
}
else
{
lean_dec(x_21);
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
lean_dec(x_23);
if (x_8 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_21);
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
lean_dec(x_21);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_12);
x_49 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_50 = lean_array_push(x_4, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_21);
return x_52;
}
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_53; 
lean_dec(x_21);
lean_dec(x_12);
x_53 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_53 == 0)
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_5);
x_55 = 0;
x_56 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_54, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_5);
lean_inc(x_7);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_5);
x_60 = 0;
x_61 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_59, x_60);
return x_61;
}
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_5);
lean_inc(x_10);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_10);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_5);
x_65 = 0;
x_66 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_64, x_65);
return x_66;
}
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_5);
x_68 = 0;
x_69 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_67, x_68);
return x_69;
}
}
}
else
{
lean_dec(x_23);
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_21);
lean_dec(x_12);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_5);
lean_inc(x_10);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_eq(x_7, x_10);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_12);
x_73 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_74 = lean_array_push(x_4, x_12);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_21);
return x_76;
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec(x_21);
lean_dec(x_12);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_5);
x_78 = 0;
x_79 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_77, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; 
lean_dec(x_21);
lean_dec(x_12);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_4);
lean_ctor_set(x_80, 1, x_5);
x_81 = 0;
x_82 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_80, x_81);
return x_82;
}
}
}
}
case 1:
{
lean_dec(x_22);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_83; 
lean_dec(x_6);
x_83 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_83 == 0)
{
if (x_8 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_5);
x_85 = 0;
x_86 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_84, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_4);
lean_ctor_set(x_87, 1, x_5);
lean_inc(x_7);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_7);
return x_88;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; 
lean_dec(x_21);
lean_dec(x_12);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_89, 1, x_5);
x_90 = 0;
x_91 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_89, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_inc(x_12);
x_92 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_93 = lean_array_push(x_4, x_12);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_21);
return x_95;
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_5);
lean_inc(x_7);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_7);
return x_97;
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_4);
lean_ctor_set(x_98, 1, x_5);
x_99 = 0;
x_100 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_98, x_99);
return x_100;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_101; 
x_101 = lean_nat_dec_eq(x_7, x_10);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc(x_12);
x_102 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_103 = lean_array_push(x_4, x_12);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_21);
return x_105;
}
else
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
lean_dec(x_21);
lean_dec(x_12);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_4);
lean_ctor_set(x_106, 1, x_5);
x_107 = 0;
x_108 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_106, x_107);
return x_108;
}
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; 
lean_dec(x_21);
lean_dec(x_12);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_4);
lean_ctor_set(x_109, 1, x_5);
x_110 = 0;
x_111 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_109, x_110);
return x_111;
}
}
}
}
case 1:
{
uint8_t x_112; lean_object* x_113; 
lean_dec(x_23);
lean_dec(x_21);
x_112 = lean_nat_dec_eq(x_7, x_10);
if (x_112 == 0)
{
lean_object* x_124; 
x_124 = lean_box(0);
x_113 = x_124;
goto block_123;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_12);
lean_dec(x_6);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_4);
lean_ctor_set(x_125, 1, x_5);
lean_inc(x_7);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
}
else
{
lean_object* x_127; 
x_127 = lean_box(0);
x_113 = x_127;
goto block_123;
}
}
else
{
lean_object* x_128; 
x_128 = lean_box(0);
x_113 = x_128;
goto block_123;
}
}
block_123:
{
lean_dec(x_113);
if (x_112 == 0)
{
lean_object* x_114; 
x_114 = lean_box(0);
x_13 = x_114;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_115; 
x_115 = lean_box(0);
x_13 = x_115;
goto block_19;
}
else
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; 
lean_dec(x_12);
lean_dec(x_6);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_4);
lean_ctor_set(x_116, 1, x_5);
x_117 = 0;
x_118 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_116, x_117);
return x_118;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; 
lean_dec(x_12);
lean_dec(x_6);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_4);
lean_ctor_set(x_119, 1, x_5);
x_120 = 0;
x_121 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_119, x_120);
return x_121;
}
else
{
lean_object* x_122; 
x_122 = lean_box(0);
x_13 = x_122;
goto block_19;
}
}
}
}
}
default: 
{
uint8_t x_129; lean_object* x_130; 
lean_dec(x_23);
lean_dec(x_21);
x_129 = lean_nat_dec_eq(x_7, x_10);
if (x_129 == 0)
{
lean_object* x_141; 
x_141 = lean_box(0);
x_130 = x_141;
goto block_140;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_12);
lean_dec(x_6);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_5);
lean_inc(x_7);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_7);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_130 = x_144;
goto block_140;
}
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_130 = x_145;
goto block_140;
}
}
block_140:
{
lean_dec(x_130);
if (x_129 == 0)
{
lean_object* x_131; 
x_131 = lean_box(0);
x_13 = x_131;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_13 = x_132;
goto block_19;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_12);
lean_dec(x_6);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_4);
lean_ctor_set(x_133, 1, x_5);
x_134 = 0;
x_135 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_133, x_134);
return x_135;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_12);
lean_dec(x_6);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_4);
lean_ctor_set(x_136, 1, x_5);
x_137 = 0;
x_138 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_136, x_137);
return x_138;
}
else
{
lean_object* x_139; 
x_139 = lean_box(0);
x_13 = x_139;
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
lean_dec(x_22);
switch (lean_obj_tag(x_23)) {
case 0:
{
uint8_t x_146; 
lean_dec(x_6);
x_146 = lean_ctor_get_uint8(x_23, 0);
lean_dec(x_23);
if (x_146 == 0)
{
if (x_8 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_5);
x_148 = 0;
x_149 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_147, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_5);
lean_inc(x_7);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_7);
return x_151;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_152; uint8_t x_153; lean_object* x_154; 
lean_dec(x_21);
lean_dec(x_12);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_4);
lean_ctor_set(x_152, 1, x_5);
x_153 = 0;
x_154 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_152, x_153);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_inc(x_12);
x_155 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_156 = lean_array_push(x_4, x_12);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_21);
return x_158;
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_4);
lean_ctor_set(x_159, 1, x_5);
lean_inc(x_7);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_7);
return x_160;
}
else
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_5);
x_162 = 0;
x_163 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_161, x_162);
return x_163;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_164; 
x_164 = lean_nat_dec_eq(x_7, x_10);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_inc(x_12);
x_165 = l_Std_Sat_AIG_Cache_insert___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_4, x_5, x_12);
x_166 = lean_array_push(x_4, x_12);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_21);
return x_168;
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; 
lean_dec(x_21);
lean_dec(x_12);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_4);
lean_ctor_set(x_169, 1, x_5);
x_170 = 0;
x_171 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_169, x_170);
return x_171;
}
}
else
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
lean_dec(x_21);
lean_dec(x_12);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_4);
lean_ctor_set(x_172, 1, x_5);
x_173 = 0;
x_174 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_172, x_173);
return x_174;
}
}
}
}
case 1:
{
uint8_t x_175; lean_object* x_176; 
lean_dec(x_23);
lean_dec(x_21);
x_175 = lean_nat_dec_eq(x_7, x_10);
if (x_175 == 0)
{
lean_object* x_187; 
x_187 = lean_box(0);
x_176 = x_187;
goto block_186;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_12);
lean_dec(x_6);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_4);
lean_ctor_set(x_188, 1, x_5);
lean_inc(x_7);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_7);
return x_189;
}
else
{
lean_object* x_190; 
x_190 = lean_box(0);
x_176 = x_190;
goto block_186;
}
}
else
{
lean_object* x_191; 
x_191 = lean_box(0);
x_176 = x_191;
goto block_186;
}
}
block_186:
{
lean_dec(x_176);
if (x_175 == 0)
{
lean_object* x_177; 
x_177 = lean_box(0);
x_13 = x_177;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_178; 
x_178 = lean_box(0);
x_13 = x_178;
goto block_19;
}
else
{
lean_object* x_179; uint8_t x_180; lean_object* x_181; 
lean_dec(x_12);
lean_dec(x_6);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_4);
lean_ctor_set(x_179, 1, x_5);
x_180 = 0;
x_181 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_179, x_180);
return x_181;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; 
lean_dec(x_12);
lean_dec(x_6);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_4);
lean_ctor_set(x_182, 1, x_5);
x_183 = 0;
x_184 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_182, x_183);
return x_184;
}
else
{
lean_object* x_185; 
x_185 = lean_box(0);
x_13 = x_185;
goto block_19;
}
}
}
}
}
default: 
{
uint8_t x_192; lean_object* x_193; 
lean_dec(x_23);
lean_dec(x_21);
x_192 = lean_nat_dec_eq(x_7, x_10);
if (x_192 == 0)
{
lean_object* x_204; 
x_204 = lean_box(0);
x_193 = x_204;
goto block_203;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_12);
lean_dec(x_6);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_4);
lean_ctor_set(x_205, 1, x_5);
lean_inc(x_7);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_7);
return x_206;
}
else
{
lean_object* x_207; 
x_207 = lean_box(0);
x_193 = x_207;
goto block_203;
}
}
else
{
lean_object* x_208; 
x_208 = lean_box(0);
x_193 = x_208;
goto block_203;
}
}
block_203:
{
lean_dec(x_193);
if (x_192 == 0)
{
lean_object* x_194; 
x_194 = lean_box(0);
x_13 = x_194;
goto block_19;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_195; 
x_195 = lean_box(0);
x_13 = x_195;
goto block_19;
}
else
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; 
lean_dec(x_12);
lean_dec(x_6);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_4);
lean_ctor_set(x_196, 1, x_5);
x_197 = 0;
x_198 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_196, x_197);
return x_198;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_199; uint8_t x_200; lean_object* x_201; 
lean_dec(x_12);
lean_dec(x_6);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_4);
lean_ctor_set(x_199, 1, x_5);
x_200 = 0;
x_201 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_199, x_200);
return x_201;
}
else
{
lean_object* x_202; 
x_202 = lean_box(0);
x_13 = x_202;
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
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_12);
lean_dec(x_6);
x_209 = lean_ctor_get(x_20, 0);
lean_inc(x_209);
lean_dec(x_20);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_4);
lean_ctor_set(x_210, 1, x_5);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
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
