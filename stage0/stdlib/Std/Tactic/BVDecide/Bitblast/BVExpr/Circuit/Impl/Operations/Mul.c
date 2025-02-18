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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg___boxed(lean_object*, lean_object*);
uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(lean_object*);
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object*, lean_object*);
static uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1;
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object*, lean_object*, uint8_t);
static uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__1(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_fget(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
if (x_3 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = 0;
return x_10;
}
}
}
static lean_object* _init_l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1;
return x_2;
}
}
static uint64_t _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 0;
x_2 = 13;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 0;
x_2 = 11;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(lean_object* x_1) {
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
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1;
return x_3;
}
else
{
uint64_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2;
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
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_4);
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
x_26 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__12___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__13(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__11(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_1, x_2, x_8);
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
x_14 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_1, x_2, x_13);
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
static lean_object* _init_l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_6, 0, x_2);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_6);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_8, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_5, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 0);
lean_dec(x_26);
x_27 = lean_array_get_size(x_4);
lean_inc(x_6);
x_28 = lean_array_push(x_4, x_6);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_6, x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_22);
x_33 = lean_array_uset(x_8, x_21, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_33);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_31);
lean_ctor_set(x_1, 0, x_28);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_27);
return x_41;
}
else
{
lean_object* x_42; 
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_31);
lean_ctor_set(x_1, 0, x_28);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_box(0);
x_44 = lean_array_uset(x_8, x_21, x_43);
lean_inc(x_27);
x_45 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_6, x_27, x_22);
x_46 = lean_array_uset(x_44, x_21, x_45);
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_1, 0, x_28);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_27);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_5);
x_48 = lean_array_get_size(x_4);
lean_inc(x_6);
x_49 = lean_array_push(x_4, x_6);
x_50 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_6, x_22);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_7, x_51);
lean_dec(x_7);
lean_inc(x_48);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_6);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_22);
x_54 = lean_array_uset(x_8, x_21, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_mul(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_49);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_48);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_48);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_box(0);
x_67 = lean_array_uset(x_8, x_21, x_66);
lean_inc(x_48);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_6, x_48, x_22);
x_69 = lean_array_uset(x_67, x_21, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_1, 1, x_70);
lean_ctor_set(x_1, 0, x_49);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_48);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = lean_ctor_get(x_23, 0);
lean_inc(x_72);
lean_dec(x_23);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_1);
x_76 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_76, 0, x_2);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_array_get_size(x_78);
x_80 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_76);
x_81 = 32;
x_82 = lean_uint64_shift_right(x_80, x_81);
x_83 = lean_uint64_xor(x_80, x_82);
x_84 = 16;
x_85 = lean_uint64_shift_right(x_83, x_84);
x_86 = lean_uint64_xor(x_83, x_85);
x_87 = lean_uint64_to_usize(x_86);
x_88 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_89 = 1;
x_90 = lean_usize_sub(x_88, x_89);
x_91 = lean_usize_land(x_87, x_90);
x_92 = lean_array_uget(x_78, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(x_76, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
x_95 = lean_array_get_size(x_74);
lean_inc(x_76);
x_96 = lean_array_push(x_74, x_76);
x_97 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_76, x_92);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_77, x_98);
lean_dec(x_77);
lean_inc(x_95);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_76);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_92);
x_101 = lean_array_uset(x_78, x_91, x_100);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_mul(x_99, x_102);
x_104 = lean_unsigned_to_nat(3u);
x_105 = lean_nat_div(x_103, x_104);
lean_dec(x_103);
x_106 = lean_array_get_size(x_101);
x_107 = lean_nat_dec_le(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_101);
if (lean_is_scalar(x_94)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_94;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_96);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_95);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
if (lean_is_scalar(x_94)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_94;
}
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_101);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_96);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_box(0);
x_116 = lean_array_uset(x_78, x_91, x_115);
lean_inc(x_95);
x_117 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_76, x_95, x_92);
x_118 = lean_array_uset(x_116, x_91, x_117);
if (lean_is_scalar(x_94)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_94;
}
lean_ctor_set(x_119, 0, x_77);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_96);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_95);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_92);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
x_122 = lean_ctor_get(x_93, 0);
lean_inc(x_122);
lean_dec(x_93);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_74);
lean_ctor_set(x_123, 1, x_75);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_2, x_17);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_2, x_4, x_5, x_7, lean_box(0), x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; size_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; 
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
x_97 = lean_ctor_get(x_5, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_5, 1);
lean_inc(x_98);
x_99 = lean_array_get_size(x_98);
x_100 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_12);
x_101 = 32;
x_102 = lean_uint64_shift_right(x_100, x_101);
x_103 = lean_uint64_xor(x_100, x_102);
x_104 = 16;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = lean_uint64_to_usize(x_106);
x_108 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_109 = 1;
x_110 = lean_usize_sub(x_108, x_109);
x_111 = lean_usize_land(x_107, x_110);
x_112 = lean_array_uget(x_98, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__7(x_12, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_array_fget(x_4, x_7);
x_115 = lean_array_fget(x_4, x_10);
switch (lean_obj_tag(x_114)) {
case 0:
{
uint8_t x_116; 
lean_dec(x_6);
x_116 = lean_ctor_get_uint8(x_114, 0);
lean_dec(x_114);
if (x_116 == 0)
{
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_117; 
x_117 = lean_ctor_get_uint8(x_115, 0);
lean_dec(x_115);
if (x_117 == 0)
{
if (x_8 == 0)
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_4);
lean_ctor_set(x_118, 1, x_5);
x_119 = 0;
x_120 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_118, x_119);
return x_120;
}
else
{
if (x_11 == 0)
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_4);
lean_ctor_set(x_121, 1, x_5);
x_122 = 0;
x_123 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_121, x_122);
return x_123;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_5);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_5, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_5, 0);
lean_dec(x_126);
x_127 = lean_array_get_size(x_4);
lean_inc(x_12);
x_128 = lean_array_push(x_4, x_12);
x_129 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_97, x_130);
lean_dec(x_97);
lean_inc(x_127);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_12);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_112);
x_133 = lean_array_uset(x_98, x_111, x_132);
x_134 = lean_unsigned_to_nat(4u);
x_135 = lean_nat_mul(x_131, x_134);
x_136 = lean_unsigned_to_nat(3u);
x_137 = lean_nat_div(x_135, x_136);
lean_dec(x_135);
x_138 = lean_array_get_size(x_133);
x_139 = lean_nat_dec_le(x_137, x_138);
lean_dec(x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_133);
lean_ctor_set(x_5, 1, x_140);
lean_ctor_set(x_5, 0, x_131);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_128);
lean_ctor_set(x_141, 1, x_5);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_127);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_ctor_set(x_5, 1, x_133);
lean_ctor_set(x_5, 0, x_131);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_128);
lean_ctor_set(x_143, 1, x_5);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_127);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_box(0);
x_146 = lean_array_uset(x_98, x_111, x_145);
lean_inc(x_127);
x_147 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_127, x_112);
x_148 = lean_array_uset(x_146, x_111, x_147);
lean_ctor_set(x_5, 1, x_148);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_128);
lean_ctor_set(x_149, 1, x_5);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_127);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_5);
x_151 = lean_array_get_size(x_4);
lean_inc(x_12);
x_152 = lean_array_push(x_4, x_12);
x_153 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_add(x_97, x_154);
lean_dec(x_97);
lean_inc(x_151);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_12);
lean_ctor_set(x_156, 1, x_151);
lean_ctor_set(x_156, 2, x_112);
x_157 = lean_array_uset(x_98, x_111, x_156);
x_158 = lean_unsigned_to_nat(4u);
x_159 = lean_nat_mul(x_155, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_div(x_159, x_160);
lean_dec(x_159);
x_162 = lean_array_get_size(x_157);
x_163 = lean_nat_dec_le(x_161, x_162);
lean_dec(x_162);
lean_dec(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_157);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_152);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_151);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_155);
lean_ctor_set(x_168, 1, x_157);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_152);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_151);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_box(0);
x_172 = lean_array_uset(x_98, x_111, x_171);
lean_inc(x_151);
x_173 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_151, x_112);
x_174 = lean_array_uset(x_172, x_111, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_97);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_152);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_151);
return x_177;
}
}
}
}
}
else
{
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
if (x_8 == 0)
{
lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_4);
lean_ctor_set(x_178, 1, x_5);
x_179 = 0;
x_180 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_178, x_179);
return x_180;
}
else
{
if (x_11 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_4);
lean_ctor_set(x_181, 1, x_5);
lean_inc(x_10);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_10);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; lean_object* x_185; 
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_4);
lean_ctor_set(x_183, 1, x_5);
x_184 = 0;
x_185 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_183, x_184);
return x_185;
}
}
}
}
else
{
lean_dec(x_115);
if (x_8 == 0)
{
lean_object* x_186; uint8_t x_187; lean_object* x_188; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_4);
lean_ctor_set(x_186, 1, x_5);
x_187 = 0;
x_188 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_186, x_187);
return x_188;
}
else
{
if (x_11 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_4);
lean_ctor_set(x_189, 1, x_5);
lean_inc(x_10);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_10);
return x_190;
}
else
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_5);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_5, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_5, 0);
lean_dec(x_193);
x_194 = lean_array_get_size(x_4);
lean_inc(x_12);
x_195 = lean_array_push(x_4, x_12);
x_196 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_97, x_197);
lean_dec(x_97);
lean_inc(x_194);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_12);
lean_ctor_set(x_199, 1, x_194);
lean_ctor_set(x_199, 2, x_112);
x_200 = lean_array_uset(x_98, x_111, x_199);
x_201 = lean_unsigned_to_nat(4u);
x_202 = lean_nat_mul(x_198, x_201);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_div(x_202, x_203);
lean_dec(x_202);
x_205 = lean_array_get_size(x_200);
x_206 = lean_nat_dec_le(x_204, x_205);
lean_dec(x_205);
lean_dec(x_204);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_200);
lean_ctor_set(x_5, 1, x_207);
lean_ctor_set(x_5, 0, x_198);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_195);
lean_ctor_set(x_208, 1, x_5);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_194);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_ctor_set(x_5, 1, x_200);
lean_ctor_set(x_5, 0, x_198);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_195);
lean_ctor_set(x_210, 1, x_5);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_194);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_box(0);
x_213 = lean_array_uset(x_98, x_111, x_212);
lean_inc(x_194);
x_214 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_194, x_112);
x_215 = lean_array_uset(x_213, x_111, x_214);
lean_ctor_set(x_5, 1, x_215);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_195);
lean_ctor_set(x_216, 1, x_5);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_194);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_5);
x_218 = lean_array_get_size(x_4);
lean_inc(x_12);
x_219 = lean_array_push(x_4, x_12);
x_220 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_97, x_221);
lean_dec(x_97);
lean_inc(x_218);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_12);
lean_ctor_set(x_223, 1, x_218);
lean_ctor_set(x_223, 2, x_112);
x_224 = lean_array_uset(x_98, x_111, x_223);
x_225 = lean_unsigned_to_nat(4u);
x_226 = lean_nat_mul(x_222, x_225);
x_227 = lean_unsigned_to_nat(3u);
x_228 = lean_nat_div(x_226, x_227);
lean_dec(x_226);
x_229 = lean_array_get_size(x_224);
x_230 = lean_nat_dec_le(x_228, x_229);
lean_dec(x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_224);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_222);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_219);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_218);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_222);
lean_ctor_set(x_235, 1, x_224);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_219);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_218);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_box(0);
x_239 = lean_array_uset(x_98, x_111, x_238);
lean_inc(x_218);
x_240 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_218, x_112);
x_241 = lean_array_uset(x_239, x_111, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_97);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_219);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_218);
return x_244;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_245; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_245 = lean_ctor_get_uint8(x_115, 0);
lean_dec(x_115);
if (x_245 == 0)
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_4);
lean_ctor_set(x_246, 1, x_5);
x_247 = 0;
x_248 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_246, x_247);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_4);
lean_ctor_set(x_249, 1, x_5);
lean_inc(x_7);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_7);
return x_250;
}
}
else
{
lean_object* x_251; uint8_t x_252; lean_object* x_253; 
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_4);
lean_ctor_set(x_251, 1, x_5);
x_252 = 0;
x_253 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_251, x_252);
return x_253;
}
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_4);
lean_ctor_set(x_254, 1, x_5);
lean_inc(x_10);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_10);
return x_255;
}
else
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_4);
lean_ctor_set(x_256, 1, x_5);
x_257 = 0;
x_258 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_256, x_257);
return x_258;
}
}
else
{
lean_object* x_259; uint8_t x_260; lean_object* x_261; 
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_4);
lean_ctor_set(x_259, 1, x_5);
x_260 = 0;
x_261 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_259, x_260);
return x_261;
}
}
}
else
{
lean_dec(x_115);
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_4);
lean_ctor_set(x_262, 1, x_5);
lean_inc(x_10);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_10);
return x_263;
}
else
{
uint8_t x_264; 
x_264 = lean_nat_dec_eq(x_7, x_10);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_5);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_5, 1);
lean_dec(x_266);
x_267 = lean_ctor_get(x_5, 0);
lean_dec(x_267);
x_268 = lean_array_get_size(x_4);
lean_inc(x_12);
x_269 = lean_array_push(x_4, x_12);
x_270 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_97, x_271);
lean_dec(x_97);
lean_inc(x_268);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_12);
lean_ctor_set(x_273, 1, x_268);
lean_ctor_set(x_273, 2, x_112);
x_274 = lean_array_uset(x_98, x_111, x_273);
x_275 = lean_unsigned_to_nat(4u);
x_276 = lean_nat_mul(x_272, x_275);
x_277 = lean_unsigned_to_nat(3u);
x_278 = lean_nat_div(x_276, x_277);
lean_dec(x_276);
x_279 = lean_array_get_size(x_274);
x_280 = lean_nat_dec_le(x_278, x_279);
lean_dec(x_279);
lean_dec(x_278);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_274);
lean_ctor_set(x_5, 1, x_281);
lean_ctor_set(x_5, 0, x_272);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_269);
lean_ctor_set(x_282, 1, x_5);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_268);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_ctor_set(x_5, 1, x_274);
lean_ctor_set(x_5, 0, x_272);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_269);
lean_ctor_set(x_284, 1, x_5);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_268);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_286 = lean_box(0);
x_287 = lean_array_uset(x_98, x_111, x_286);
lean_inc(x_268);
x_288 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_268, x_112);
x_289 = lean_array_uset(x_287, x_111, x_288);
lean_ctor_set(x_5, 1, x_289);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_269);
lean_ctor_set(x_290, 1, x_5);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_268);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
lean_dec(x_5);
x_292 = lean_array_get_size(x_4);
lean_inc(x_12);
x_293 = lean_array_push(x_4, x_12);
x_294 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_295 = lean_unsigned_to_nat(1u);
x_296 = lean_nat_add(x_97, x_295);
lean_dec(x_97);
lean_inc(x_292);
x_297 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_297, 0, x_12);
lean_ctor_set(x_297, 1, x_292);
lean_ctor_set(x_297, 2, x_112);
x_298 = lean_array_uset(x_98, x_111, x_297);
x_299 = lean_unsigned_to_nat(4u);
x_300 = lean_nat_mul(x_296, x_299);
x_301 = lean_unsigned_to_nat(3u);
x_302 = lean_nat_div(x_300, x_301);
lean_dec(x_300);
x_303 = lean_array_get_size(x_298);
x_304 = lean_nat_dec_le(x_302, x_303);
lean_dec(x_303);
lean_dec(x_302);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_296);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_293);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_292);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_296);
lean_ctor_set(x_309, 1, x_298);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_293);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_292);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_box(0);
x_313 = lean_array_uset(x_98, x_111, x_312);
lean_inc(x_292);
x_314 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_292, x_112);
x_315 = lean_array_uset(x_313, x_111, x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_97);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_293);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_292);
return x_318;
}
}
}
else
{
lean_object* x_319; uint8_t x_320; lean_object* x_321; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_4);
lean_ctor_set(x_319, 1, x_5);
x_320 = 0;
x_321 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_319, x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; uint8_t x_323; lean_object* x_324; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_4);
lean_ctor_set(x_322, 1, x_5);
x_323 = 0;
x_324 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_322, x_323);
return x_324;
}
}
}
}
case 1:
{
lean_dec(x_114);
switch (lean_obj_tag(x_115)) {
case 0:
{
uint8_t x_325; 
lean_dec(x_6);
x_325 = lean_ctor_get_uint8(x_115, 0);
lean_dec(x_115);
if (x_325 == 0)
{
if (x_8 == 0)
{
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_326; uint8_t x_327; lean_object* x_328; 
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_4);
lean_ctor_set(x_326, 1, x_5);
x_327 = 0;
x_328 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_326, x_327);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_4);
lean_ctor_set(x_329, 1, x_5);
lean_inc(x_7);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_7);
return x_330;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_331; uint8_t x_332; lean_object* x_333; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_4);
lean_ctor_set(x_331, 1, x_5);
x_332 = 0;
x_333 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_331, x_332);
return x_333;
}
else
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_5);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_335 = lean_ctor_get(x_5, 1);
lean_dec(x_335);
x_336 = lean_ctor_get(x_5, 0);
lean_dec(x_336);
x_337 = lean_array_get_size(x_4);
lean_inc(x_12);
x_338 = lean_array_push(x_4, x_12);
x_339 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_nat_add(x_97, x_340);
lean_dec(x_97);
lean_inc(x_337);
x_342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_342, 0, x_12);
lean_ctor_set(x_342, 1, x_337);
lean_ctor_set(x_342, 2, x_112);
x_343 = lean_array_uset(x_98, x_111, x_342);
x_344 = lean_unsigned_to_nat(4u);
x_345 = lean_nat_mul(x_341, x_344);
x_346 = lean_unsigned_to_nat(3u);
x_347 = lean_nat_div(x_345, x_346);
lean_dec(x_345);
x_348 = lean_array_get_size(x_343);
x_349 = lean_nat_dec_le(x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_343);
lean_ctor_set(x_5, 1, x_350);
lean_ctor_set(x_5, 0, x_341);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_338);
lean_ctor_set(x_351, 1, x_5);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_337);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_ctor_set(x_5, 1, x_343);
lean_ctor_set(x_5, 0, x_341);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_338);
lean_ctor_set(x_353, 1, x_5);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_337);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_355 = lean_box(0);
x_356 = lean_array_uset(x_98, x_111, x_355);
lean_inc(x_337);
x_357 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_337, x_112);
x_358 = lean_array_uset(x_356, x_111, x_357);
lean_ctor_set(x_5, 1, x_358);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_338);
lean_ctor_set(x_359, 1, x_5);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_337);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
lean_dec(x_5);
x_361 = lean_array_get_size(x_4);
lean_inc(x_12);
x_362 = lean_array_push(x_4, x_12);
x_363 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_364 = lean_unsigned_to_nat(1u);
x_365 = lean_nat_add(x_97, x_364);
lean_dec(x_97);
lean_inc(x_361);
x_366 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_366, 0, x_12);
lean_ctor_set(x_366, 1, x_361);
lean_ctor_set(x_366, 2, x_112);
x_367 = lean_array_uset(x_98, x_111, x_366);
x_368 = lean_unsigned_to_nat(4u);
x_369 = lean_nat_mul(x_365, x_368);
x_370 = lean_unsigned_to_nat(3u);
x_371 = lean_nat_div(x_369, x_370);
lean_dec(x_369);
x_372 = lean_array_get_size(x_367);
x_373 = lean_nat_dec_le(x_371, x_372);
lean_dec(x_372);
lean_dec(x_371);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_367);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_362);
lean_ctor_set(x_376, 1, x_375);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_361);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_365);
lean_ctor_set(x_378, 1, x_367);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_362);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_361);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_381 = lean_box(0);
x_382 = lean_array_uset(x_98, x_111, x_381);
lean_inc(x_361);
x_383 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_361, x_112);
x_384 = lean_array_uset(x_382, x_111, x_383);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_97);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_362);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_361);
return x_387;
}
}
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_4);
lean_ctor_set(x_388, 1, x_5);
lean_inc(x_7);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_7);
return x_389;
}
else
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_4);
lean_ctor_set(x_390, 1, x_5);
x_391 = 0;
x_392 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_390, x_391);
return x_392;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_393; 
x_393 = lean_nat_dec_eq(x_7, x_10);
if (x_393 == 0)
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_5);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_395 = lean_ctor_get(x_5, 1);
lean_dec(x_395);
x_396 = lean_ctor_get(x_5, 0);
lean_dec(x_396);
x_397 = lean_array_get_size(x_4);
lean_inc(x_12);
x_398 = lean_array_push(x_4, x_12);
x_399 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_400 = lean_unsigned_to_nat(1u);
x_401 = lean_nat_add(x_97, x_400);
lean_dec(x_97);
lean_inc(x_397);
x_402 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_402, 0, x_12);
lean_ctor_set(x_402, 1, x_397);
lean_ctor_set(x_402, 2, x_112);
x_403 = lean_array_uset(x_98, x_111, x_402);
x_404 = lean_unsigned_to_nat(4u);
x_405 = lean_nat_mul(x_401, x_404);
x_406 = lean_unsigned_to_nat(3u);
x_407 = lean_nat_div(x_405, x_406);
lean_dec(x_405);
x_408 = lean_array_get_size(x_403);
x_409 = lean_nat_dec_le(x_407, x_408);
lean_dec(x_408);
lean_dec(x_407);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_403);
lean_ctor_set(x_5, 1, x_410);
lean_ctor_set(x_5, 0, x_401);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_398);
lean_ctor_set(x_411, 1, x_5);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_397);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_ctor_set(x_5, 1, x_403);
lean_ctor_set(x_5, 0, x_401);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_398);
lean_ctor_set(x_413, 1, x_5);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_397);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_415 = lean_box(0);
x_416 = lean_array_uset(x_98, x_111, x_415);
lean_inc(x_397);
x_417 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_397, x_112);
x_418 = lean_array_uset(x_416, x_111, x_417);
lean_ctor_set(x_5, 1, x_418);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_398);
lean_ctor_set(x_419, 1, x_5);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_397);
return x_420;
}
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_5);
x_421 = lean_array_get_size(x_4);
lean_inc(x_12);
x_422 = lean_array_push(x_4, x_12);
x_423 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_424 = lean_unsigned_to_nat(1u);
x_425 = lean_nat_add(x_97, x_424);
lean_dec(x_97);
lean_inc(x_421);
x_426 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_426, 0, x_12);
lean_ctor_set(x_426, 1, x_421);
lean_ctor_set(x_426, 2, x_112);
x_427 = lean_array_uset(x_98, x_111, x_426);
x_428 = lean_unsigned_to_nat(4u);
x_429 = lean_nat_mul(x_425, x_428);
x_430 = lean_unsigned_to_nat(3u);
x_431 = lean_nat_div(x_429, x_430);
lean_dec(x_429);
x_432 = lean_array_get_size(x_427);
x_433 = lean_nat_dec_le(x_431, x_432);
lean_dec(x_432);
lean_dec(x_431);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_427);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_425);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_422);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_421);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_425);
lean_ctor_set(x_438, 1, x_427);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_422);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_421);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_441 = lean_box(0);
x_442 = lean_array_uset(x_98, x_111, x_441);
lean_inc(x_421);
x_443 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_421, x_112);
x_444 = lean_array_uset(x_442, x_111, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_97);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_422);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_421);
return x_447;
}
}
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_4);
lean_ctor_set(x_448, 1, x_5);
x_449 = 0;
x_450 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_448, x_449);
return x_450;
}
}
else
{
lean_object* x_451; uint8_t x_452; lean_object* x_453; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_4);
lean_ctor_set(x_451, 1, x_5);
x_452 = 0;
x_453 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_451, x_452);
return x_453;
}
}
}
}
case 1:
{
uint8_t x_454; lean_object* x_455; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
x_454 = lean_nat_dec_eq(x_7, x_10);
if (x_454 == 0)
{
lean_object* x_466; 
x_466 = lean_box(0);
x_455 = x_466;
goto block_465;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_12);
lean_dec(x_6);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_4);
lean_ctor_set(x_467, 1, x_5);
lean_inc(x_7);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_7);
return x_468;
}
else
{
lean_object* x_469; 
x_469 = lean_box(0);
x_455 = x_469;
goto block_465;
}
}
else
{
lean_object* x_470; 
x_470 = lean_box(0);
x_455 = x_470;
goto block_465;
}
}
block_465:
{
lean_dec(x_455);
if (x_454 == 0)
{
lean_object* x_456; 
x_456 = lean_box(0);
x_13 = x_456;
goto block_96;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_457; 
x_457 = lean_box(0);
x_13 = x_457;
goto block_96;
}
else
{
lean_object* x_458; uint8_t x_459; lean_object* x_460; 
lean_dec(x_12);
lean_dec(x_6);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_4);
lean_ctor_set(x_458, 1, x_5);
x_459 = 0;
x_460 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_458, x_459);
return x_460;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_461; uint8_t x_462; lean_object* x_463; 
lean_dec(x_12);
lean_dec(x_6);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_4);
lean_ctor_set(x_461, 1, x_5);
x_462 = 0;
x_463 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_461, x_462);
return x_463;
}
else
{
lean_object* x_464; 
x_464 = lean_box(0);
x_13 = x_464;
goto block_96;
}
}
}
}
}
default: 
{
uint8_t x_471; lean_object* x_472; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
x_471 = lean_nat_dec_eq(x_7, x_10);
if (x_471 == 0)
{
lean_object* x_483; 
x_483 = lean_box(0);
x_472 = x_483;
goto block_482;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_12);
lean_dec(x_6);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_4);
lean_ctor_set(x_484, 1, x_5);
lean_inc(x_7);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_7);
return x_485;
}
else
{
lean_object* x_486; 
x_486 = lean_box(0);
x_472 = x_486;
goto block_482;
}
}
else
{
lean_object* x_487; 
x_487 = lean_box(0);
x_472 = x_487;
goto block_482;
}
}
block_482:
{
lean_dec(x_472);
if (x_471 == 0)
{
lean_object* x_473; 
x_473 = lean_box(0);
x_13 = x_473;
goto block_96;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_474; 
x_474 = lean_box(0);
x_13 = x_474;
goto block_96;
}
else
{
lean_object* x_475; uint8_t x_476; lean_object* x_477; 
lean_dec(x_12);
lean_dec(x_6);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_4);
lean_ctor_set(x_475, 1, x_5);
x_476 = 0;
x_477 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_475, x_476);
return x_477;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_478; uint8_t x_479; lean_object* x_480; 
lean_dec(x_12);
lean_dec(x_6);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_4);
lean_ctor_set(x_478, 1, x_5);
x_479 = 0;
x_480 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_478, x_479);
return x_480;
}
else
{
lean_object* x_481; 
x_481 = lean_box(0);
x_13 = x_481;
goto block_96;
}
}
}
}
}
}
}
default: 
{
lean_dec(x_114);
switch (lean_obj_tag(x_115)) {
case 0:
{
uint8_t x_488; 
lean_dec(x_6);
x_488 = lean_ctor_get_uint8(x_115, 0);
lean_dec(x_115);
if (x_488 == 0)
{
if (x_8 == 0)
{
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_489; uint8_t x_490; lean_object* x_491; 
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_4);
lean_ctor_set(x_489, 1, x_5);
x_490 = 0;
x_491 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_489, x_490);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_4);
lean_ctor_set(x_492, 1, x_5);
lean_inc(x_7);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_7);
return x_493;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_494; uint8_t x_495; lean_object* x_496; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_4);
lean_ctor_set(x_494, 1, x_5);
x_495 = 0;
x_496 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_494, x_495);
return x_496;
}
else
{
uint8_t x_497; 
x_497 = !lean_is_exclusive(x_5);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_498 = lean_ctor_get(x_5, 1);
lean_dec(x_498);
x_499 = lean_ctor_get(x_5, 0);
lean_dec(x_499);
x_500 = lean_array_get_size(x_4);
lean_inc(x_12);
x_501 = lean_array_push(x_4, x_12);
x_502 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_503 = lean_unsigned_to_nat(1u);
x_504 = lean_nat_add(x_97, x_503);
lean_dec(x_97);
lean_inc(x_500);
x_505 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_505, 0, x_12);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_112);
x_506 = lean_array_uset(x_98, x_111, x_505);
x_507 = lean_unsigned_to_nat(4u);
x_508 = lean_nat_mul(x_504, x_507);
x_509 = lean_unsigned_to_nat(3u);
x_510 = lean_nat_div(x_508, x_509);
lean_dec(x_508);
x_511 = lean_array_get_size(x_506);
x_512 = lean_nat_dec_le(x_510, x_511);
lean_dec(x_511);
lean_dec(x_510);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_506);
lean_ctor_set(x_5, 1, x_513);
lean_ctor_set(x_5, 0, x_504);
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_501);
lean_ctor_set(x_514, 1, x_5);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_500);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; 
lean_ctor_set(x_5, 1, x_506);
lean_ctor_set(x_5, 0, x_504);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_501);
lean_ctor_set(x_516, 1, x_5);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_500);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_518 = lean_box(0);
x_519 = lean_array_uset(x_98, x_111, x_518);
lean_inc(x_500);
x_520 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_500, x_112);
x_521 = lean_array_uset(x_519, x_111, x_520);
lean_ctor_set(x_5, 1, x_521);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_501);
lean_ctor_set(x_522, 1, x_5);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_500);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; uint8_t x_526; 
lean_dec(x_5);
x_524 = lean_array_get_size(x_4);
lean_inc(x_12);
x_525 = lean_array_push(x_4, x_12);
x_526 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_527 = lean_unsigned_to_nat(1u);
x_528 = lean_nat_add(x_97, x_527);
lean_dec(x_97);
lean_inc(x_524);
x_529 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_529, 0, x_12);
lean_ctor_set(x_529, 1, x_524);
lean_ctor_set(x_529, 2, x_112);
x_530 = lean_array_uset(x_98, x_111, x_529);
x_531 = lean_unsigned_to_nat(4u);
x_532 = lean_nat_mul(x_528, x_531);
x_533 = lean_unsigned_to_nat(3u);
x_534 = lean_nat_div(x_532, x_533);
lean_dec(x_532);
x_535 = lean_array_get_size(x_530);
x_536 = lean_nat_dec_le(x_534, x_535);
lean_dec(x_535);
lean_dec(x_534);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_537 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_530);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_528);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_525);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_524);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_528);
lean_ctor_set(x_541, 1, x_530);
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_525);
lean_ctor_set(x_542, 1, x_541);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_524);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_544 = lean_box(0);
x_545 = lean_array_uset(x_98, x_111, x_544);
lean_inc(x_524);
x_546 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_524, x_112);
x_547 = lean_array_uset(x_545, x_111, x_546);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_97);
lean_ctor_set(x_548, 1, x_547);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_525);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_524);
return x_550;
}
}
}
}
}
else
{
if (x_8 == 0)
{
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
if (x_11 == 0)
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_4);
lean_ctor_set(x_551, 1, x_5);
lean_inc(x_7);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_7);
return x_552;
}
else
{
lean_object* x_553; uint8_t x_554; lean_object* x_555; 
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_4);
lean_ctor_set(x_553, 1, x_5);
x_554 = 0;
x_555 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_553, x_554);
return x_555;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_556; 
x_556 = lean_nat_dec_eq(x_7, x_10);
if (x_556 == 0)
{
uint8_t x_557; 
x_557 = !lean_is_exclusive(x_5);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_558 = lean_ctor_get(x_5, 1);
lean_dec(x_558);
x_559 = lean_ctor_get(x_5, 0);
lean_dec(x_559);
x_560 = lean_array_get_size(x_4);
lean_inc(x_12);
x_561 = lean_array_push(x_4, x_12);
x_562 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_563 = lean_unsigned_to_nat(1u);
x_564 = lean_nat_add(x_97, x_563);
lean_dec(x_97);
lean_inc(x_560);
x_565 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_565, 0, x_12);
lean_ctor_set(x_565, 1, x_560);
lean_ctor_set(x_565, 2, x_112);
x_566 = lean_array_uset(x_98, x_111, x_565);
x_567 = lean_unsigned_to_nat(4u);
x_568 = lean_nat_mul(x_564, x_567);
x_569 = lean_unsigned_to_nat(3u);
x_570 = lean_nat_div(x_568, x_569);
lean_dec(x_568);
x_571 = lean_array_get_size(x_566);
x_572 = lean_nat_dec_le(x_570, x_571);
lean_dec(x_571);
lean_dec(x_570);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_566);
lean_ctor_set(x_5, 1, x_573);
lean_ctor_set(x_5, 0, x_564);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_561);
lean_ctor_set(x_574, 1, x_5);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_560);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_ctor_set(x_5, 1, x_566);
lean_ctor_set(x_5, 0, x_564);
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_561);
lean_ctor_set(x_576, 1, x_5);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_560);
return x_577;
}
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_578 = lean_box(0);
x_579 = lean_array_uset(x_98, x_111, x_578);
lean_inc(x_560);
x_580 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_560, x_112);
x_581 = lean_array_uset(x_579, x_111, x_580);
lean_ctor_set(x_5, 1, x_581);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_561);
lean_ctor_set(x_582, 1, x_5);
x_583 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_560);
return x_583;
}
}
else
{
lean_object* x_584; lean_object* x_585; uint8_t x_586; 
lean_dec(x_5);
x_584 = lean_array_get_size(x_4);
lean_inc(x_12);
x_585 = lean_array_push(x_4, x_12);
x_586 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_112);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_587 = lean_unsigned_to_nat(1u);
x_588 = lean_nat_add(x_97, x_587);
lean_dec(x_97);
lean_inc(x_584);
x_589 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_589, 0, x_12);
lean_ctor_set(x_589, 1, x_584);
lean_ctor_set(x_589, 2, x_112);
x_590 = lean_array_uset(x_98, x_111, x_589);
x_591 = lean_unsigned_to_nat(4u);
x_592 = lean_nat_mul(x_588, x_591);
x_593 = lean_unsigned_to_nat(3u);
x_594 = lean_nat_div(x_592, x_593);
lean_dec(x_592);
x_595 = lean_array_get_size(x_590);
x_596 = lean_nat_dec_le(x_594, x_595);
lean_dec(x_595);
lean_dec(x_594);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_597 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_590);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_588);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_585);
lean_ctor_set(x_599, 1, x_598);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_584);
return x_600;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_588);
lean_ctor_set(x_601, 1, x_590);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_585);
lean_ctor_set(x_602, 1, x_601);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_584);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_604 = lean_box(0);
x_605 = lean_array_uset(x_98, x_111, x_604);
lean_inc(x_584);
x_606 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_584, x_112);
x_607 = lean_array_uset(x_605, x_111, x_606);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_97);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_585);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_584);
return x_610;
}
}
}
else
{
lean_object* x_611; uint8_t x_612; lean_object* x_613; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_4);
lean_ctor_set(x_611, 1, x_5);
x_612 = 0;
x_613 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_611, x_612);
return x_613;
}
}
else
{
lean_object* x_614; uint8_t x_615; lean_object* x_616; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_4);
lean_ctor_set(x_614, 1, x_5);
x_615 = 0;
x_616 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_614, x_615);
return x_616;
}
}
}
}
case 1:
{
uint8_t x_617; lean_object* x_618; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
x_617 = lean_nat_dec_eq(x_7, x_10);
if (x_617 == 0)
{
lean_object* x_629; 
x_629 = lean_box(0);
x_618 = x_629;
goto block_628;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_630; lean_object* x_631; 
lean_dec(x_12);
lean_dec(x_6);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_4);
lean_ctor_set(x_630, 1, x_5);
lean_inc(x_7);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_7);
return x_631;
}
else
{
lean_object* x_632; 
x_632 = lean_box(0);
x_618 = x_632;
goto block_628;
}
}
else
{
lean_object* x_633; 
x_633 = lean_box(0);
x_618 = x_633;
goto block_628;
}
}
block_628:
{
lean_dec(x_618);
if (x_617 == 0)
{
lean_object* x_619; 
x_619 = lean_box(0);
x_13 = x_619;
goto block_96;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_620; 
x_620 = lean_box(0);
x_13 = x_620;
goto block_96;
}
else
{
lean_object* x_621; uint8_t x_622; lean_object* x_623; 
lean_dec(x_12);
lean_dec(x_6);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_4);
lean_ctor_set(x_621, 1, x_5);
x_622 = 0;
x_623 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_621, x_622);
return x_623;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_624; uint8_t x_625; lean_object* x_626; 
lean_dec(x_12);
lean_dec(x_6);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_4);
lean_ctor_set(x_624, 1, x_5);
x_625 = 0;
x_626 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_624, x_625);
return x_626;
}
else
{
lean_object* x_627; 
x_627 = lean_box(0);
x_13 = x_627;
goto block_96;
}
}
}
}
}
default: 
{
uint8_t x_634; lean_object* x_635; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
x_634 = lean_nat_dec_eq(x_7, x_10);
if (x_634 == 0)
{
lean_object* x_646; 
x_646 = lean_box(0);
x_635 = x_646;
goto block_645;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_647; lean_object* x_648; 
lean_dec(x_12);
lean_dec(x_6);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_4);
lean_ctor_set(x_647, 1, x_5);
lean_inc(x_7);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_7);
return x_648;
}
else
{
lean_object* x_649; 
x_649 = lean_box(0);
x_635 = x_649;
goto block_645;
}
}
else
{
lean_object* x_650; 
x_650 = lean_box(0);
x_635 = x_650;
goto block_645;
}
}
block_645:
{
lean_dec(x_635);
if (x_634 == 0)
{
lean_object* x_636; 
x_636 = lean_box(0);
x_13 = x_636;
goto block_96;
}
else
{
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_637; 
x_637 = lean_box(0);
x_13 = x_637;
goto block_96;
}
else
{
lean_object* x_638; uint8_t x_639; lean_object* x_640; 
lean_dec(x_12);
lean_dec(x_6);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_4);
lean_ctor_set(x_638, 1, x_5);
x_639 = 0;
x_640 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_638, x_639);
return x_640;
}
}
else
{
if (x_8 == 0)
{
lean_object* x_641; uint8_t x_642; lean_object* x_643; 
lean_dec(x_12);
lean_dec(x_6);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_4);
lean_ctor_set(x_641, 1, x_5);
x_642 = 0;
x_643 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_641, x_642);
return x_643;
}
else
{
lean_object* x_644; 
x_644 = lean_box(0);
x_13 = x_644;
goto block_96;
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
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_112);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_12);
lean_dec(x_6);
x_651 = lean_ctor_get(x_113, 0);
lean_inc(x_651);
lean_dec(x_113);
x_652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_652, 0, x_4);
lean_ctor_set(x_652, 1, x_5);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
block_96:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_4);
lean_inc(x_12);
x_15 = lean_array_push(x_4, x_12);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_array_get_size(x_18);
x_20 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_12);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_18, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_17, x_34);
lean_dec(x_17);
lean_inc(x_14);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_14);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_array_uset(x_18, x_31, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_37);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_35);
if (lean_is_scalar(x_6)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_6;
}
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_14);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_ctor_set(x_5, 1, x_37);
lean_ctor_set(x_5, 0, x_35);
if (lean_is_scalar(x_6)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_6;
}
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_14);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_box(0);
x_50 = lean_array_uset(x_18, x_31, x_49);
lean_inc(x_14);
x_51 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_14, x_32);
x_52 = lean_array_uset(x_50, x_31, x_51);
lean_ctor_set(x_5, 1, x_52);
if (lean_is_scalar(x_6)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_6;
}
lean_ctor_set(x_53, 0, x_15);
lean_ctor_set(x_53, 1, x_5);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_array_get_size(x_56);
x_58 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_12);
x_59 = 32;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = 16;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_67 = 1;
x_68 = lean_usize_sub(x_66, x_67);
x_69 = lean_usize_land(x_65, x_68);
x_70 = lean_array_uget(x_56, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_12, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_55, x_72);
lean_dec(x_55);
lean_inc(x_14);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_12);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 2, x_70);
x_75 = lean_array_uset(x_56, x_69, x_74);
x_76 = lean_unsigned_to_nat(4u);
x_77 = lean_nat_mul(x_73, x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_div(x_77, x_78);
lean_dec(x_77);
x_80 = lean_array_get_size(x_75);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__10(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_6)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_6;
}
lean_ctor_set(x_84, 0, x_15);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_14);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_75);
if (lean_is_scalar(x_6)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_6;
}
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_14);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_box(0);
x_90 = lean_array_uset(x_56, x_69, x_89);
lean_inc(x_14);
x_91 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__14(x_12, x_14, x_70);
x_92 = lean_array_uset(x_90, x_69, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_55);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_6)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_6;
}
lean_ctor_set(x_94, 0, x_15);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_14);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
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
x_17 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_2);
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
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_10, x_15);
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
x_22 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_17, x_21);
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
x_29 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_28);
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
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_30, x_35);
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
x_42 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_37, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_2);
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
x_16 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_10, x_6);
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
x_19 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_13, x_18);
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
x_26 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_1, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_27, x_22);
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
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_30, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_8, x_10);
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
x_15 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_13);
x_18 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_17, x_15);
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
x_22 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_19, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg(x_4, x_2, lean_box(0));
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__17(x_2, x_15);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = 0;
x_5 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_6, x_8, x_9, x_11, lean_box(0), x_7, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = 1;
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_3);
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
x_11 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_8, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_11, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_9);
x_17 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_16, x_14);
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
x_21 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_18, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__28(x_2, x_15);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_2, x_8, lean_box(0), x_4, x_5, x_6, x_7);
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = 0;
x_11 = l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_2, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_5);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_5);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_1, x_2, x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_6);
lean_ctor_set(x_13, 0, x_6);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_15, x_13);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_6);
x_20 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_17, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_2 = x_21;
x_5 = x_24;
x_6 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
lean_inc(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_26, x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_6);
x_33 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_30, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_5, x_36);
lean_dec(x_5);
x_2 = x_34;
x_5 = x_37;
x_6 = x_35;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_Sat_AIG_isConstant___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__1(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_400____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__8(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_mkGateCached_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__18(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__22(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__23(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__15(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Sat_AIG_RefVec_ite_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_2, x_3);
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
x_10 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_2, x_9);
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
x_4 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
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
x_14 = l_Std_Sat_AIG_RefVec_ite___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__26(x_1, x_8, x_13);
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
x_19 = l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3(x_2);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1;
x_10 = lean_array_get(x_9, x_8, x_7);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_10);
x_3 = x_12;
goto _start;
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
l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1 = _init_l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_RefVec_empty___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__3___closed__1);
l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1 = _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__1();
l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2 = _init_l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_84____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__6___closed__2();
l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___closed__1 = _init_l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
