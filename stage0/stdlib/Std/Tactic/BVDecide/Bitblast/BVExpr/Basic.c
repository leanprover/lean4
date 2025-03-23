// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
// Imports: Init.Data.Hashable Init.Data.BitVec Init.Data.RArray Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(uint8_t);
static lean_object* l_Std_Tactic_BVDecide_BVPred_instToString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14;
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4;
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___rarg(lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_RArray_getImpl___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355____boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____boxed(lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVExpr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5;
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__10;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17;
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVExpr(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7;
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6;
static lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2;
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3;
uint64_t l_BitVec_hash(lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__9;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr_match__1_splitter____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr_match__1_splitter____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85____boxed(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___closed__2;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11;
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__13;
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__12;
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_append___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8;
static lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9;
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___rarg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit;
static lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_instToString;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_instToString;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__5;
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion(lean_object*);
lean_object* l_BitVec_toHex(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
static lean_object* l_Std_Tactic_BVDecide_instHashableBVBit___closed__1;
lean_object* lean_nat_lor(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__11;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instToString;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = 0;
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_of_nat(x_3);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_of_nat(x_4);
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBit() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBit___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_4, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_5, x_8);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVBit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3;
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("w", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("idx", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l___private_Init_Data_Repr_0__Nat_reprFast(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_8);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
x_29 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_8);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_8);
return x_44;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instReprBVBit___closed__1;
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_4 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__3;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
uint64_t x_4; 
x_4 = 2;
return x_4;
}
case 3:
{
uint64_t x_5; 
x_5 = 3;
return x_5;
}
case 4:
{
uint64_t x_6; 
x_6 = 4;
return x_6;
}
case 5:
{
uint64_t x_7; 
x_7 = 5;
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = 6;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBinOp() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 2;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_nat_dec_le(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 4;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 3;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_1, x_10);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 6;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 5;
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_1);
x_4 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&&", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("||", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("^", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/ᵤ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("%ᵤ", 4, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6;
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_5; 
x_5 = lean_nat_land(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_nat_lor(x_3, x_4);
return x_6;
}
case 2:
{
lean_object* x_7; 
x_7 = lean_nat_lxor(x_3, x_4);
return x_7;
}
case 3:
{
lean_object* x_8; 
x_8 = l_BitVec_add(x_1, x_3, x_4);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = l_BitVec_mul(x_1, x_3, x_4);
return x_9;
}
case 5:
{
lean_object* x_10; 
x_10 = lean_nat_div(x_3, x_4);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = lean_nat_mod(x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 2;
x_9 = lean_uint64_of_nat(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = 3;
x_13 = lean_uint64_of_nat(x_11);
x_14 = lean_uint64_mix_hash(x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVUnOp() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_nat_dec_eq(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_nat_dec_eq(x_9, x_10);
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
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_nat_dec_eq(x_13, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("~", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rotL ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rotR ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">>a ", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_9);
x_11 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_17 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVUnOp_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; 
x_4 = l_BitVec_not(x_1, x_3);
lean_dec(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_BitVec_rotateLeft(x_1, x_3, x_5);
lean_dec(x_3);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_BitVec_rotateRight(x_1, x_3, x_7);
lean_dec(x_3);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_BitVec_sshiftRight(x_1, x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_nat_dec_eq(x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_nat_dec_eq(x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_nat_dec_eq(x_12, x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_13, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
x_1 = x_12;
x_2 = x_14;
x_3 = x_17;
goto _start;
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_29 = lean_ctor_get(x_3, 2);
x_30 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_24, x_27);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_25, x_28);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
else
{
x_2 = x_26;
x_3 = x_29;
goto _start;
}
}
}
else
{
uint8_t x_35; 
x_35 = 0;
return x_35;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_36, x_38);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 0;
return x_41;
}
else
{
x_2 = x_37;
x_3 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
x_43 = 0;
return x_43;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_ctor_get(x_3, 3);
x_51 = lean_ctor_get(x_3, 4);
x_52 = lean_nat_dec_eq(x_44, x_48);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = 0;
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_eq(x_45, x_49);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
return x_55;
}
else
{
uint8_t x_56; 
x_56 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_44, x_46, x_50);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = 0;
return x_57;
}
else
{
x_1 = x_45;
x_2 = x_47;
x_3 = x_51;
goto _start;
}
}
}
}
else
{
uint8_t x_59; 
x_59 = 0;
return x_59;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_ctor_get(x_3, 0);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_ctor_get(x_3, 3);
x_66 = lean_nat_dec_eq(x_60, x_63);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = 0;
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_eq(x_61, x_64);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 0;
return x_69;
}
else
{
x_1 = x_60;
x_2 = x_62;
x_3 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_71; 
x_71 = 0;
return x_71;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_ctor_get(x_2, 2);
x_74 = lean_ctor_get(x_2, 3);
x_75 = lean_ctor_get(x_3, 1);
x_76 = lean_ctor_get(x_3, 2);
x_77 = lean_ctor_get(x_3, 3);
x_78 = lean_nat_dec_eq(x_72, x_75);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = 0;
return x_79;
}
else
{
uint8_t x_80; 
x_80 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_73, x_76);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = 0;
return x_81;
}
else
{
x_1 = x_72;
x_2 = x_74;
x_3 = x_77;
goto _start;
}
}
}
else
{
uint8_t x_83; 
x_83 = 0;
return x_83;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
x_86 = lean_ctor_get(x_2, 3);
x_87 = lean_ctor_get(x_3, 1);
x_88 = lean_ctor_get(x_3, 2);
x_89 = lean_ctor_get(x_3, 3);
x_90 = lean_nat_dec_eq(x_84, x_87);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = 0;
return x_91;
}
else
{
uint8_t x_92; 
x_92 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_85, x_88);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
return x_93;
}
else
{
x_1 = x_84;
x_2 = x_86;
x_3 = x_89;
goto _start;
}
}
}
else
{
uint8_t x_95; 
x_95 = 0;
return x_95;
}
}
default: 
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_2, 1);
x_97 = lean_ctor_get(x_2, 2);
x_98 = lean_ctor_get(x_2, 3);
x_99 = lean_ctor_get(x_3, 1);
x_100 = lean_ctor_get(x_3, 2);
x_101 = lean_ctor_get(x_3, 3);
x_102 = lean_nat_dec_eq(x_96, x_99);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = 0;
return x_103;
}
else
{
uint8_t x_104; 
x_104 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_97, x_100);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = 0;
return x_105;
}
else
{
x_1 = x_96;
x_2 = x_98;
x_3 = x_101;
goto _start;
}
}
}
else
{
uint8_t x_107; 
x_107 = 0;
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_2355_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_instDecidableEqBVExpr(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = 0;
x_5 = lean_uint64_of_nat(x_1);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_of_nat(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = 1;
x_11 = lean_uint64_of_nat(x_1);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_BitVec_hash(x_1, x_9);
x_14 = lean_uint64_mix_hash(x_12, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 3);
x_18 = 2;
x_19 = lean_uint64_of_nat(x_15);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_uint64_of_nat(x_16);
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = lean_uint64_of_nat(x_1);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_15, x_17);
x_26 = lean_uint64_mix_hash(x_24, x_25);
return x_26;
}
case 3:
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_29 = lean_ctor_get(x_2, 2);
x_30 = 3;
x_31 = lean_uint64_of_nat(x_1);
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_27);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(x_28);
x_36 = lean_uint64_mix_hash(x_34, x_35);
x_37 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_29);
x_38 = lean_uint64_mix_hash(x_36, x_37);
return x_38;
}
case 4:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; 
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
x_41 = 4;
x_42 = lean_uint64_of_nat(x_1);
x_43 = lean_uint64_mix_hash(x_41, x_42);
x_44 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(x_39);
x_45 = lean_uint64_mix_hash(x_43, x_44);
x_46 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_40);
x_47 = lean_uint64_mix_hash(x_45, x_46);
return x_47;
}
case 5:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 3);
x_51 = lean_ctor_get(x_2, 4);
x_52 = 5;
x_53 = lean_uint64_of_nat(x_48);
x_54 = lean_uint64_mix_hash(x_52, x_53);
x_55 = lean_uint64_of_nat(x_49);
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_57 = lean_uint64_of_nat(x_1);
x_58 = lean_uint64_mix_hash(x_56, x_57);
x_59 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_48, x_50);
x_60 = lean_uint64_mix_hash(x_58, x_59);
x_61 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_49, x_51);
x_62 = lean_uint64_mix_hash(x_60, x_61);
x_63 = 0;
x_64 = lean_uint64_mix_hash(x_62, x_63);
return x_64;
}
case 6:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 2);
x_67 = lean_ctor_get(x_2, 3);
x_68 = 6;
x_69 = lean_uint64_of_nat(x_65);
x_70 = lean_uint64_mix_hash(x_68, x_69);
x_71 = lean_uint64_of_nat(x_1);
x_72 = lean_uint64_mix_hash(x_70, x_71);
x_73 = lean_uint64_of_nat(x_66);
x_74 = lean_uint64_mix_hash(x_72, x_73);
x_75 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_65, x_67);
x_76 = lean_uint64_mix_hash(x_74, x_75);
x_77 = 0;
x_78 = lean_uint64_mix_hash(x_76, x_77);
return x_78;
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; 
x_79 = lean_ctor_get(x_2, 1);
x_80 = lean_ctor_get(x_2, 2);
x_81 = lean_ctor_get(x_2, 3);
x_82 = 7;
x_83 = lean_uint64_of_nat(x_1);
x_84 = lean_uint64_mix_hash(x_82, x_83);
x_85 = lean_uint64_of_nat(x_79);
x_86 = lean_uint64_mix_hash(x_84, x_85);
x_87 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_80);
x_88 = lean_uint64_mix_hash(x_86, x_87);
x_89 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_79, x_81);
x_90 = lean_uint64_mix_hash(x_88, x_89);
return x_90;
}
case 8:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; 
x_91 = lean_ctor_get(x_2, 1);
x_92 = lean_ctor_get(x_2, 2);
x_93 = lean_ctor_get(x_2, 3);
x_94 = 8;
x_95 = lean_uint64_of_nat(x_1);
x_96 = lean_uint64_mix_hash(x_94, x_95);
x_97 = lean_uint64_of_nat(x_91);
x_98 = lean_uint64_mix_hash(x_96, x_97);
x_99 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_92);
x_100 = lean_uint64_mix_hash(x_98, x_99);
x_101 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_91, x_93);
x_102 = lean_uint64_mix_hash(x_100, x_101);
return x_102;
}
default: 
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; 
x_103 = lean_ctor_get(x_2, 1);
x_104 = lean_ctor_get(x_2, 2);
x_105 = lean_ctor_get(x_2, 3);
x_106 = 9;
x_107 = lean_uint64_of_nat(x_1);
x_108 = lean_uint64_mix_hash(x_106, x_107);
x_109 = lean_uint64_of_nat(x_103);
x_110 = lean_uint64_mix_hash(x_108, x_109);
x_111 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_104);
x_112 = lean_uint64_mix_hash(x_110, x_111);
x_113 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_103, x_105);
x_114 = lean_uint64_mix_hash(x_112, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ++ ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(replicate ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" << ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" >> ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" >>a ", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = l_BitVec_toHex(x_1, x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__4;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Std_Format_defWidth;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_format_pretty(x_19, x_20, x_21, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_BitVec_toHex(x_1, x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__4;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_Format_defWidth;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_format_pretty(x_32, x_33, x_34, x_34);
return x_35;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Std_Tactic_BVDecide_BVExpr_toString(x_36, x_38);
x_40 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__5;
x_47 = lean_string_append(x_45, x_46);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__3;
x_51 = lean_string_append(x_49, x_50);
return x_51;
}
case 3:
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
lean_dec(x_2);
lean_inc(x_1);
x_55 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_52);
x_56 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_53);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = lean_string_append(x_61, x_58);
x_63 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_54);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_66 = lean_string_append(x_64, x_65);
return x_66;
}
case 4:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 2);
lean_inc(x_68);
lean_dec(x_2);
x_69 = l_Std_Tactic_BVDecide_BVUnOp_toString(x_67);
x_70 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_68);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
x_76 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_77 = lean_string_append(x_75, x_76);
return x_77;
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 4);
lean_inc(x_81);
lean_dec(x_2);
x_82 = l_Std_Tactic_BVDecide_BVExpr_toString(x_78, x_80);
x_83 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__9;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Std_Tactic_BVDecide_BVExpr_toString(x_79, x_81);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_90 = lean_string_append(x_88, x_89);
return x_90;
}
case 6:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 3);
lean_inc(x_93);
lean_dec(x_2);
x_94 = l___private_Init_Data_Repr_0__Nat_reprFast(x_92);
x_95 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__10;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_Std_Tactic_BVDecide_BVExpr_toString(x_91, x_93);
x_100 = lean_string_append(x_98, x_99);
lean_dec(x_99);
x_101 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_102 = lean_string_append(x_100, x_101);
return x_102;
}
case 7:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 3);
lean_inc(x_105);
lean_dec(x_2);
x_106 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_104);
x_107 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__11;
x_110 = lean_string_append(x_108, x_109);
x_111 = l_Std_Tactic_BVDecide_BVExpr_toString(x_103, x_105);
x_112 = lean_string_append(x_110, x_111);
lean_dec(x_111);
x_113 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_114 = lean_string_append(x_112, x_113);
return x_114;
}
case 8:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_2, 3);
lean_inc(x_117);
lean_dec(x_2);
x_118 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_116);
x_119 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_120 = lean_string_append(x_119, x_118);
lean_dec(x_118);
x_121 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__12;
x_122 = lean_string_append(x_120, x_121);
x_123 = l_Std_Tactic_BVDecide_BVExpr_toString(x_115, x_117);
x_124 = lean_string_append(x_122, x_123);
lean_dec(x_123);
x_125 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_126 = lean_string_append(x_124, x_125);
return x_126;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_127 = lean_ctor_get(x_2, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_2, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_2, 3);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_128);
x_131 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_132 = lean_string_append(x_131, x_130);
lean_dec(x_130);
x_133 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__13;
x_134 = lean_string_append(x_132, x_133);
x_135 = l_Std_Tactic_BVDecide_BVExpr_toString(x_127, x_129);
x_136 = lean_string_append(x_134, x_135);
lean_dec(x_135);
x_137 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_138 = lean_string_append(x_136, x_137);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Lean_RArray_getImpl___rarg(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_BitVec_setWidth(x_6, x_1, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
return x_10;
}
}
case 1:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 3);
x_15 = l_Std_Tactic_BVDecide_BVExpr_eval(x_12, x_2, x_14);
x_16 = l_BitVec_extractLsb_x27___rarg(x_13, x_1, x_15);
lean_dec(x_15);
return x_16;
}
case 3:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_17);
x_21 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_19);
x_22 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_18, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_24);
x_26 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_23, x_25);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_3, 3);
x_30 = lean_ctor_get(x_3, 4);
x_31 = l_Std_Tactic_BVDecide_BVExpr_eval(x_27, x_2, x_29);
x_32 = l_Std_Tactic_BVDecide_BVExpr_eval(x_28, x_2, x_30);
x_33 = l_BitVec_append___rarg(x_28, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = l_Std_Tactic_BVDecide_BVExpr_eval(x_34, x_2, x_36);
x_38 = l_BitVec_replicate(x_34, x_35, x_37);
lean_dec(x_37);
return x_38;
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_ctor_get(x_3, 3);
x_42 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_40);
x_43 = l_Std_Tactic_BVDecide_BVExpr_eval(x_39, x_2, x_41);
x_44 = l_BitVec_shiftLeft(x_1, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
return x_44;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_46);
x_49 = l_Std_Tactic_BVDecide_BVExpr_eval(x_45, x_2, x_47);
x_50 = lean_nat_shiftr(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_3, 1);
x_52 = lean_ctor_get(x_3, 2);
x_53 = lean_ctor_get(x_3, 3);
x_54 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_52);
x_55 = l_Std_Tactic_BVDecide_BVExpr_eval(x_51, x_2, x_53);
x_56 = l_BitVec_sshiftRight(x_1, x_54, x_55);
lean_dec(x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr_match__1_splitter____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_3, x_1, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_2(x_4, x_1, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_4(x_5, x_1, x_17, x_18, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(x_22);
x_25 = lean_apply_4(x_6, x_1, x_21, x_24, x_23);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_3(x_7, x_1, x_26, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 4);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_apply_6(x_8, x_1, x_29, x_30, x_31, x_32, lean_box(0));
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_apply_5(x_9, x_1, x_34, x_35, x_36, lean_box(0));
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 3);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_apply_4(x_10, x_1, x_38, x_39, x_40);
return x_41;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 3);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_apply_4(x_11, x_1, x_42, x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 3);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_apply_4(x_12, x_1, x_46, x_47, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr_match__1_splitter____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVExpr_match__1_splitter____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_8992____rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinPred_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("==", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<u", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinPred_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinPred_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_2, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinPred_eval___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Std_Tactic_BVDecide_BVBinPred_eval___rarg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_eval(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_3);
x_7 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_4);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_string_append(x_12, x_9);
x_14 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_toString(x_18, x_19);
x_22 = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_20);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Std_Tactic_BVDecide_instToStringBVBit___closed__3;
x_29 = lean_string_append(x_27, x_28);
return x_29;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_BVPred_instToString___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_4);
x_8 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_6);
x_9 = l_Std_Tactic_BVDecide_BVBinPred_eval___rarg(x_5, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = l_Std_Tactic_BVDecide_BVExpr_eval(x_10, x_1, x_11);
x_14 = l_Nat_testBit(x_13, x_12);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVPred_eval(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_eval___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Tactic_BVDecide_BoolExpr_eval___rarg(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_instHashableBVBit___closed__1 = _init_l_Std_Tactic_BVDecide_instHashableBVBit___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBit___closed__1);
l_Std_Tactic_BVDecide_instHashableBVBit = _init_l_Std_Tactic_BVDecide_instHashableBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBit);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__1);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__2);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__3);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__4);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__5);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__6);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__7);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__8);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__9);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__10);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__11);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__12);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__13);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__14);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__15);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__16);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__17);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__18);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__19);
l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20 = _init_l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____closed__20);
l_Std_Tactic_BVDecide_instReprBVBit___closed__1 = _init_l_Std_Tactic_BVDecide_instReprBVBit___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit___closed__1);
l_Std_Tactic_BVDecide_instReprBVBit = _init_l_Std_Tactic_BVDecide_instReprBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit);
l_Std_Tactic_BVDecide_instToStringBVBit___closed__1 = _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instToStringBVBit___closed__1);
l_Std_Tactic_BVDecide_instToStringBVBit___closed__2 = _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_instToStringBVBit___closed__2);
l_Std_Tactic_BVDecide_instToStringBVBit___closed__3 = _init_l_Std_Tactic_BVDecide_instToStringBVBit___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_instToStringBVBit___closed__3);
l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1 = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1);
l_Std_Tactic_BVDecide_instInhabitedBVBit = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit);
l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1 = _init_l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_noConfusion___rarg___closed__1);
l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1 = _init_l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__1);
l_Std_Tactic_BVDecide_instHashableBVBinOp = _init_l_Std_Tactic_BVDecide_instHashableBVBinOp();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBinOp);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6);
l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7 = _init_l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__7);
l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1 = _init_l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__1);
l_Std_Tactic_BVDecide_BVBinOp_instToString = _init_l_Std_Tactic_BVDecide_BVBinOp_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_instToString);
l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1 = _init_l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__1);
l_Std_Tactic_BVDecide_instHashableBVUnOp = _init_l_Std_Tactic_BVDecide_instHashableBVUnOp();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVUnOp);
l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1 = _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1);
l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2 = _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2);
l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3 = _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3);
l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4 = _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4);
l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5 = _init_l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5);
l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1 = _init_l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__1);
l_Std_Tactic_BVDecide_BVUnOp_instToString = _init_l_Std_Tactic_BVDecide_BVUnOp_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_instToString);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__3 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__4 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__5 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__6 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__6();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__7 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__7();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__8 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__8();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__9 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__9();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__9);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__10 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__10();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__10);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__11 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__11();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__11);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__12 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__12();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__12);
l_Std_Tactic_BVDecide_BVExpr_toString___closed__13 = _init_l_Std_Tactic_BVDecide_BVExpr_toString___closed__13();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_toString___closed__13);
l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1 = _init_l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1);
l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2 = _init_l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__2);
l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1 = _init_l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__1);
l_Std_Tactic_BVDecide_BVBinPred_instToString = _init_l_Std_Tactic_BVDecide_BVBinPred_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinPred_instToString);
l_Std_Tactic_BVDecide_BVPred_instToString___closed__1 = _init_l_Std_Tactic_BVDecide_BVPred_instToString___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_instToString___closed__1);
l_Std_Tactic_BVDecide_BVPred_instToString = _init_l_Std_Tactic_BVDecide_BVPred_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
