// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred import Init.Omega
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
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object* v_aig_1_, lean_object* v_ref_2_){
_start:
{
lean_object* v_gate_3_; uint8_t v_invert_4_; lean_object* v_decls_5_; lean_object* v_decl_6_; 
v_gate_3_ = lean_ctor_get(v_ref_2_, 0);
v_invert_4_ = lean_ctor_get_uint8(v_ref_2_, sizeof(void*)*1);
v_decls_5_ = lean_ctor_get(v_aig_1_, 0);
v_decl_6_ = lean_array_fget_borrowed(v_decls_5_, v_gate_3_);
if (lean_obj_tag(v_decl_6_) == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_box(v_invert_4_);
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object* v_aig_10_, lean_object* v_ref_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v_aig_10_, v_ref_11_);
lean_dec_ref(v_ref_11_);
lean_dec_ref(v_aig_10_);
return v_res_12_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9(lean_object* v_x_13_){
_start:
{
switch(lean_obj_tag(v_x_13_))
{
case 0:
{
uint64_t v___x_14_; 
v___x_14_ = 0ULL;
return v___x_14_;
}
case 1:
{
lean_object* v_idx_15_; uint64_t v___x_16_; uint64_t v___x_17_; uint64_t v___x_18_; 
v_idx_15_ = lean_ctor_get(v_x_13_, 0);
v___x_16_ = 1ULL;
v___x_17_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_15_);
v___x_18_ = lean_uint64_mix_hash(v___x_16_, v___x_17_);
return v___x_18_;
}
default: 
{
lean_object* v_l_19_; lean_object* v_r_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; 
v_l_19_ = lean_ctor_get(v_x_13_, 0);
v_r_20_ = lean_ctor_get(v_x_13_, 1);
v___x_21_ = 2ULL;
v___x_22_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_19_);
v___x_23_ = lean_uint64_mix_hash(v___x_21_, v___x_22_);
v___x_24_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_20_);
v___x_25_ = lean_uint64_mix_hash(v___x_23_, v___x_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_x_26_){
_start:
{
uint64_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9(v_x_26_);
lean_dec(v_x_26_);
v_r_28_ = lean_box_uint64(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_m_29_, lean_object* v_query_30_, lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_zero_34_; uint8_t v_isZero_35_; 
v_zero_34_ = lean_unsigned_to_nat(0u);
v_isZero_35_ = lean_nat_dec_eq(v_x_32_, v_zero_34_);
if (v_isZero_35_ == 1)
{
lean_dec(v_x_33_);
lean_dec(v_x_32_);
lean_dec(v_query_30_);
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(2);
return v___x_36_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_val_37_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v_x_31_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_val_37_);
lean_dec(v_x_31_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_val_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
else
{
lean_object* v_keyArray_45_; lean_object* v_valueArray_46_; lean_object* v___x_47_; uint8_t v_isSome_48_; 
v_keyArray_45_ = lean_ctor_get(v_m_29_, 1);
v_valueArray_46_ = lean_ctor_get(v_m_29_, 2);
v___x_47_ = lean_array_fget_borrowed(v_keyArray_45_, v_x_33_);
v_isSome_48_ = lean_noption_is_some(v___x_47_);
if (v_isSome_48_ == 0)
{
lean_dec(v_x_32_);
lean_dec(v_query_30_);
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_49_, 0, v_x_33_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
lean_dec(v_x_33_);
v_val_50_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v_x_31_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_val_50_);
lean_dec(v_x_31_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_val_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
else
{
lean_object* v_one_58_; lean_object* v_n_59_; lean_object* v___y_61_; 
v_one_58_ = lean_unsigned_to_nat(1u);
v_n_59_ = lean_nat_sub(v_x_32_, v_one_58_);
lean_dec(v_x_32_);
if (v_isSome_48_ == 0)
{
goto v___jp_67_;
}
else
{
lean_object* v___x_69_; uint8_t v_isSome_70_; 
v___x_69_ = lean_array_fget_borrowed(v_valueArray_46_, v_x_33_);
v_isSome_70_ = lean_noption_is_some(v___x_69_);
if (v_isSome_70_ == 0)
{
goto v___jp_67_;
}
else
{
lean_object* v___x_71_; lean_object* v_val_72_; uint8_t v___x_73_; 
v___x_71_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v___x_47_);
v_val_72_ = lean_noption_get(v___x_47_);
lean_inc(v_query_30_);
lean_inc(v_val_72_);
v___x_73_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_71_, v_val_72_, v_query_30_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
lean_dec(v_val_72_);
v___x_74_ = lean_array_get_size(v_keyArray_45_);
v___x_75_ = lean_nat_add(v_x_33_, v_one_58_);
lean_dec(v_x_33_);
v___x_76_ = lean_nat_dec_lt(v___x_75_, v___x_74_);
if (v___x_76_ == 0)
{
lean_dec(v___x_75_);
v_x_32_ = v_n_59_;
v_x_33_ = v_zero_34_;
goto _start;
}
else
{
v_x_32_ = v_n_59_;
v_x_33_ = v___x_75_;
goto _start;
}
}
else
{
lean_object* v_val_79_; lean_object* v___x_80_; 
lean_dec(v_n_59_);
lean_dec(v_x_31_);
lean_dec(v_query_30_);
lean_inc(v___x_69_);
v_val_79_ = lean_noption_get(v___x_69_);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v_x_33_);
lean_ctor_set(v___x_80_, 1, v_val_72_);
lean_ctor_set(v___x_80_, 2, v_val_79_);
return v___x_80_;
}
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_array_get_size(v_keyArray_45_);
v___x_63_ = lean_nat_add(v_x_33_, v_one_58_);
lean_dec(v_x_33_);
v___x_64_ = lean_nat_dec_lt(v___x_63_, v___x_62_);
if (v___x_64_ == 0)
{
lean_dec(v___x_63_);
v_x_31_ = v___y_61_;
v_x_32_ = v_n_59_;
v_x_33_ = v_zero_34_;
goto _start;
}
else
{
v_x_31_ = v___y_61_;
v_x_32_ = v_n_59_;
v_x_33_ = v___x_63_;
goto _start;
}
}
v___jp_67_:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_68_; 
lean_inc(v_x_33_);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v_x_33_);
v___y_61_ = v___x_68_;
goto v___jp_60_;
}
else
{
v___y_61_ = v_x_31_;
goto v___jp_60_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_m_81_, lean_object* v_query_82_, lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_m_81_, v_query_82_, v_x_83_, v_x_84_, v_x_85_);
lean_dec_ref(v_m_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object* v_m_87_, lean_object* v_query_88_){
_start:
{
lean_object* v_keyArray_89_; lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v_fold_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_keyArray_89_ = lean_ctor_get(v_m_87_, 1);
v___x_90_ = lean_array_get_size(v_keyArray_89_);
v___x_91_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__9(v_query_88_);
v___x_92_ = 32ULL;
v___x_93_ = lean_uint64_shift_right(v___x_91_, v___x_92_);
v_fold_94_ = lean_uint64_xor(v___x_91_, v___x_93_);
v___x_95_ = 16ULL;
v___x_96_ = lean_uint64_shift_right(v_fold_94_, v___x_95_);
v___x_97_ = lean_uint64_xor(v_fold_94_, v___x_96_);
v___x_98_ = lean_uint64_to_usize(v___x_97_);
v___x_99_ = lean_usize_of_nat(v___x_90_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_sub(v___x_99_, v___x_100_);
v___x_102_ = lean_usize_land(v___x_98_, v___x_101_);
v___x_103_ = lean_usize_to_nat(v___x_102_);
v___x_104_ = lean_box(0);
v___x_105_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_m_87_, v_query_88_, v___x_104_, v___x_90_, v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_106_, lean_object* v_query_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_106_, v_query_107_);
lean_dec_ref(v_m_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_m_109_, lean_object* v_query_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_109_, v_query_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_index_112_; lean_object* v_key_113_; lean_object* v_value_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_index_112_ = lean_ctor_get(v___x_111_, 0);
v_key_113_ = lean_ctor_get(v___x_111_, 1);
v_value_114_ = lean_ctor_get(v___x_111_, 2);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_111_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_value_114_);
lean_inc(v_key_113_);
lean_inc(v_index_112_);
lean_dec(v___x_111_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_index_112_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_key_113_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_value_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v___x_111_);
v___x_122_ = lean_box(1);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_m_123_, lean_object* v_query_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg(v_m_123_, v_query_124_);
lean_dec_ref(v_m_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg(v_m_126_, v_a_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_value_129_; lean_object* v___x_130_; 
v_value_129_ = lean_ctor_get(v___x_128_, 2);
lean_inc(v_value_129_);
lean_dec_ref_known(v___x_128_, 3);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_value_129_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_132_, v_a_133_);
lean_dec_ref(v_m_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg(lean_object* v_b_135_, lean_object* v_acc_136_, lean_object* v_i_137_){
_start:
{
lean_object* v___y_139_; lean_object* v_keyArray_147_; lean_object* v_valueArray_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_keyArray_147_ = lean_ctor_get(v_b_135_, 1);
v_valueArray_148_ = lean_ctor_get(v_b_135_, 2);
v___x_149_ = lean_array_get_size(v_keyArray_147_);
v___x_150_ = lean_nat_dec_lt(v_i_137_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_i_137_);
return v_acc_136_;
}
else
{
lean_object* v___x_151_; uint8_t v_isSome_152_; 
v___x_151_ = lean_array_fget_borrowed(v_keyArray_147_, v_i_137_);
v_isSome_152_ = lean_noption_is_some(v___x_151_);
if (v_isSome_152_ == 0)
{
goto v___jp_143_;
}
else
{
lean_object* v___x_153_; uint8_t v_isSome_154_; 
v___x_153_ = lean_array_fget_borrowed(v_valueArray_148_, v_i_137_);
v_isSome_154_ = lean_noption_is_some(v___x_153_);
if (v_isSome_154_ == 0)
{
goto v___jp_143_;
}
else
{
lean_object* v_val_155_; lean_object* v_val_156_; lean_object* v_i_158_; lean_object* v___x_163_; 
lean_inc(v___x_151_);
v_val_155_ = lean_noption_get(v___x_151_);
lean_inc(v___x_153_);
v_val_156_ = lean_noption_get(v___x_153_);
lean_inc(v_val_155_);
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_acc_136_, v_val_155_);
switch(lean_obj_tag(v___x_163_))
{
case 0:
{
lean_object* v_index_164_; lean_object* v_size_165_; lean_object* v___x_166_; 
v_index_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_index_164_);
lean_dec_ref_known(v___x_163_, 3);
v_size_165_ = lean_ctor_get(v_acc_136_, 0);
lean_inc(v_size_165_);
v___x_166_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_136_, v_size_165_, v_index_164_, v_val_155_, v_val_156_);
lean_dec(v_index_164_);
v___y_139_ = v___x_166_;
goto v___jp_138_;
}
case 1:
{
lean_object* v_index_167_; 
v_index_167_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_index_167_);
lean_dec_ref_known(v___x_163_, 1);
v_i_158_ = v_index_167_;
goto v___jp_157_;
}
default: 
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_136_, v___x_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_index_170_; 
v_index_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_index_170_);
lean_dec_ref_known(v___x_169_, 1);
v_i_158_ = v_index_170_;
goto v___jp_157_;
}
else
{
lean_dec(v_val_156_);
lean_dec(v_val_155_);
v___y_139_ = v_acc_136_;
goto v___jp_138_;
}
}
}
v___jp_157_:
{
lean_object* v_size_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_size_159_ = lean_ctor_get(v_acc_136_, 0);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_size_159_, v___x_160_);
v___x_162_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_136_, v___x_161_, v_i_158_, v_val_155_, v_val_156_);
lean_dec(v_i_158_);
v___y_139_ = v___x_162_;
goto v___jp_138_;
}
}
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_i_137_, v___x_140_);
lean_dec(v_i_137_);
v_acc_136_ = v___y_139_;
v_i_137_ = v___x_141_;
goto _start;
}
v___jp_143_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_add(v_i_137_, v___x_144_);
lean_dec(v_i_137_);
v_i_137_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg___boxed(lean_object* v_b_171_, lean_object* v_acc_172_, lean_object* v_i_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg(v_b_171_, v_acc_172_, v_i_173_);
lean_dec_ref(v_b_171_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg(lean_object* v_init_175_, lean_object* v_b_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg(v_b_176_, v_init_175_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg___boxed(lean_object* v_init_179_, lean_object* v_b_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg(v_init_179_, v_b_180_);
lean_dec_ref(v_b_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(lean_object* v_m_182_){
_start:
{
lean_object* v_keyArray_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_cellCount_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_target_190_; lean_object* v___x_191_; 
v_keyArray_183_ = lean_ctor_get(v_m_182_, 1);
v___x_184_ = lean_array_get_size(v_keyArray_183_);
v___x_185_ = lean_unsigned_to_nat(2u);
v_cellCount_186_ = lean_nat_mul(v___x_184_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_186_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_186_);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_186_);
v_target_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_190_, 0, v___x_187_);
lean_ctor_set(v_target_190_, 1, v___x_188_);
lean_ctor_set(v_target_190_, 2, v___x_189_);
v___x_191_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg(v_target_190_, v_m_182_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(v_m_192_);
lean_dec_ref(v_m_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object* v_aig_197_, lean_object* v_input_198_){
_start:
{
lean_object* v_lhs_199_; lean_object* v_rhs_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_348_; 
v_lhs_199_ = lean_ctor_get(v_input_198_, 0);
v_rhs_200_ = lean_ctor_get(v_input_198_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_input_198_);
if (v_isSharedCheck_348_ == 0)
{
v___x_202_ = v_input_198_;
v_isShared_203_ = v_isSharedCheck_348_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_rhs_200_);
lean_inc(v_lhs_199_);
lean_dec(v_input_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_348_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_decls_204_; lean_object* v_cache_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_347_; 
v_decls_204_ = lean_ctor_get(v_aig_197_, 0);
v_cache_205_ = lean_ctor_get(v_aig_197_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_aig_197_);
if (v_isSharedCheck_347_ == 0)
{
v___x_207_ = v_aig_197_;
v_isShared_208_ = v_isSharedCheck_347_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_cache_205_);
lean_inc(v_decls_204_);
lean_dec(v_aig_197_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_347_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_gate_209_; uint8_t v_invert_210_; lean_object* v_gate_211_; uint8_t v_invert_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_decl_221_; 
v_gate_209_ = lean_ctor_get(v_lhs_199_, 0);
lean_inc(v_gate_209_);
v_invert_210_ = lean_ctor_get_uint8(v_lhs_199_, sizeof(void*)*1);
v_gate_211_ = lean_ctor_get(v_rhs_200_, 0);
v_invert_212_ = lean_ctor_get_uint8(v_rhs_200_, sizeof(void*)*1);
v___x_213_ = lean_unsigned_to_nat(2u);
v___x_214_ = lean_nat_mul(v_gate_209_, v___x_213_);
v___x_215_ = l_Bool_toNat(v_invert_210_);
v___x_216_ = lean_nat_lor(v___x_214_, v___x_215_);
lean_dec(v___x_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_nat_mul(v_gate_211_, v___x_213_);
v___x_218_ = l_Bool_toNat(v_invert_212_);
v___x_219_ = lean_nat_lor(v___x_217_, v___x_218_);
lean_dec(v___x_218_);
lean_dec(v___x_217_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 2);
lean_ctor_set(v___x_202_, 1, v___x_219_);
lean_ctor_set(v___x_202_, 0, v___x_216_);
v_decl_221_ = v___x_202_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_219_);
v_decl_221_ = v_reuseFailAlloc_346_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
lean_inc_ref(v_decl_221_);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_cache_205_, v_decl_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_224_; 
lean_inc(v_gate_211_);
lean_inc_ref(v_cache_205_);
lean_inc_ref(v_decls_204_);
if (v_isShared_208_ == 0)
{
v___x_224_ = v___x_207_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_decls_204_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_cache_205_);
v___x_224_ = v_reuseFailAlloc_331_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint8_t v___y_226_; uint8_t v___y_231_; lean_object* v_lhsVal_240_; lean_object* v_rhsVal_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_329_; 
v_lhsVal_240_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_224_, v_lhs_199_);
lean_dec_ref(v_lhs_199_);
v_rhsVal_241_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_224_, v_rhs_200_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_rhs_200_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_rhs_200_, 0);
lean_dec(v_unused_330_);
v___x_243_ = v_rhs_200_;
v_isShared_244_ = v_isSharedCheck_329_;
goto v_resetjp_242_;
}
else
{
lean_dec(v_rhs_200_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_329_;
goto v_resetjp_242_;
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v_ref_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v_ref_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_228_, 0, v___x_227_);
lean_ctor_set_uint8(v_ref_228_, sizeof(void*)*1, v___y_226_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_224_);
lean_ctor_set(v___x_229_, 1, v_ref_228_);
return v___x_229_;
}
v___jp_230_:
{
if (v___y_231_ == 0)
{
lean_dec(v_gate_209_);
v___y_226_ = v___y_231_;
goto v___jp_225_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_232_, 0, v_gate_209_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v_invert_210_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_224_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
v___jp_234_:
{
lean_object* v_ref_235_; lean_object* v___x_236_; 
v_ref_235_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0));
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_224_);
lean_ctor_set(v___x_236_, 1, v_ref_235_);
return v___x_236_;
}
v___jp_237_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_238_, 0, v_gate_211_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*1, v_invert_212_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_224_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_lhsVal_240_) == 1)
{
lean_object* v_val_245_; uint8_t v___x_246_; 
lean_del_object(v___x_243_);
lean_dec_ref(v_decl_221_);
lean_dec(v_gate_209_);
lean_dec_ref(v_cache_205_);
lean_dec_ref(v_decls_204_);
v_val_245_ = lean_ctor_get(v_lhsVal_240_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_lhsVal_240_, 1);
v___x_246_ = lean_unbox(v_val_245_);
lean_dec(v_val_245_);
if (v___x_246_ == 0)
{
lean_dec(v_rhsVal_241_);
lean_dec(v_gate_211_);
goto v___jp_234_;
}
else
{
if (lean_obj_tag(v_rhsVal_241_) == 1)
{
lean_object* v_val_247_; uint8_t v___x_248_; 
v_val_247_ = lean_ctor_get(v_rhsVal_241_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_rhsVal_241_, 1);
v___x_248_ = lean_unbox(v_val_247_);
lean_dec(v_val_247_);
if (v___x_248_ == 0)
{
lean_dec(v_gate_211_);
goto v___jp_234_;
}
else
{
goto v___jp_237_;
}
}
else
{
lean_dec(v_rhsVal_241_);
goto v___jp_237_;
}
}
}
else
{
lean_dec(v_lhsVal_240_);
if (lean_obj_tag(v_rhsVal_241_) == 1)
{
lean_object* v_val_249_; uint8_t v___x_250_; 
lean_dec_ref(v_decl_221_);
lean_dec(v_gate_211_);
lean_dec_ref(v_cache_205_);
lean_dec_ref(v_decls_204_);
v_val_249_ = lean_ctor_get(v_rhsVal_241_, 0);
lean_inc(v_val_249_);
lean_dec_ref_known(v_rhsVal_241_, 1);
v___x_250_ = lean_unbox(v_val_249_);
lean_dec(v_val_249_);
if (v___x_250_ == 0)
{
lean_del_object(v___x_243_);
lean_dec(v_gate_209_);
goto v___jp_234_;
}
else
{
lean_object* v___x_252_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_gate_209_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_gate_209_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v_invert_210_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_224_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
}
else
{
uint8_t v___x_255_; 
lean_dec(v_rhsVal_241_);
v___x_255_ = lean_nat_dec_eq(v_gate_209_, v_gate_211_);
lean_dec(v_gate_211_);
if (v___x_255_ == 0)
{
lean_object* v_g_256_; lean_object* v___y_258_; lean_object* v___y_266_; lean_object* v_i_267_; lean_object* v___y_273_; lean_object* v___y_283_; lean_object* v_i_284_; lean_object* v___x_299_; 
lean_dec_ref(v___x_224_);
lean_dec(v_gate_209_);
v_g_256_ = lean_array_get_size(v_decls_204_);
lean_inc_ref(v_decl_221_);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_cache_205_, v_decl_221_);
switch(lean_obj_tag(v___x_299_))
{
case 0:
{
lean_object* v_index_300_; lean_object* v_size_301_; lean_object* v___x_302_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 3);
v_size_301_ = lean_ctor_get(v_cache_205_, 0);
lean_inc(v_size_301_);
lean_inc_ref(v_decl_221_);
v___x_302_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_205_, v_size_301_, v_index_300_, v_decl_221_, v_g_256_);
lean_dec(v_index_300_);
v___y_258_ = v___x_302_;
goto v___jp_257_;
}
case 1:
{
lean_object* v_index_303_; lean_object* v_size_304_; lean_object* v_keyArray_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_index_303_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_299_, 1);
v_size_304_ = lean_ctor_get(v_cache_205_, 0);
v_keyArray_305_ = lean_ctor_get(v_cache_205_, 1);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_size_304_, v___x_306_);
v___x_308_ = lean_array_get_size(v_keyArray_305_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_index_303_);
goto v___jp_289_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_mul(v___x_307_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_mul(v___x_308_, v___x_312_);
v___x_314_ = lean_nat_dec_le(v___x_311_, v___x_313_);
lean_dec(v___x_313_);
lean_dec(v___x_311_);
if (v___x_314_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_index_303_);
goto v___jp_289_;
}
else
{
lean_object* v___x_315_; 
lean_inc_ref(v_decl_221_);
v___x_315_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_205_, v___x_307_, v_index_303_, v_decl_221_, v_g_256_);
lean_dec(v_index_303_);
v___y_258_ = v___x_315_;
goto v___jp_257_;
}
}
}
default: 
{
lean_object* v_size_316_; lean_object* v_keyArray_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_size_316_ = lean_ctor_get(v_cache_205_, 0);
v_keyArray_317_ = lean_ctor_get(v_cache_205_, 1);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_size_316_, v___x_318_);
v___x_320_ = lean_array_get_size(v_keyArray_317_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v___x_319_);
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(v_cache_205_);
lean_dec_ref(v_cache_205_);
v___y_273_ = v___x_322_;
goto v___jp_272_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_nat_mul(v___x_319_, v___x_323_);
lean_dec(v___x_319_);
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = lean_nat_mul(v___x_320_, v___x_325_);
v___x_327_ = lean_nat_dec_le(v___x_324_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_324_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(v_cache_205_);
lean_dec_ref(v_cache_205_);
v___y_273_ = v___x_328_;
goto v___jp_272_;
}
else
{
v___y_273_ = v_cache_205_;
goto v___jp_272_;
}
}
}
}
v___jp_257_:
{
lean_object* v_decls_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v_decls_259_ = lean_array_push(v_decls_204_, v_decl_221_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_decls_259_);
lean_ctor_set(v___x_260_, 1, v___y_258_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_g_256_);
v___x_262_ = v___x_243_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_g_256_);
v___x_262_ = v_reuseFailAlloc_264_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; 
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_255_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
return v___x_263_;
}
}
v___jp_265_:
{
lean_object* v_size_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_size_268_ = lean_ctor_get(v___y_266_, 0);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_size_268_, v___x_269_);
lean_inc_ref(v_decl_221_);
v___x_271_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_266_, v___x_270_, v_i_267_, v_decl_221_, v_g_256_);
lean_dec(v_i_267_);
v___y_258_ = v___x_271_;
goto v___jp_257_;
}
v___jp_272_:
{
lean_object* v___x_274_; 
lean_inc_ref(v_decl_221_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v___y_273_, v_decl_221_);
switch(lean_obj_tag(v___x_274_))
{
case 0:
{
lean_object* v_index_275_; lean_object* v_size_276_; lean_object* v___x_277_; 
v_index_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_index_275_);
lean_dec_ref_known(v___x_274_, 3);
v_size_276_ = lean_ctor_get(v___y_273_, 0);
lean_inc(v_size_276_);
lean_inc_ref(v_decl_221_);
v___x_277_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_273_, v_size_276_, v_index_275_, v_decl_221_, v_g_256_);
lean_dec(v_index_275_);
v___y_258_ = v___x_277_;
goto v___jp_257_;
}
case 1:
{
lean_object* v_index_278_; 
v_index_278_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_index_278_);
lean_dec_ref_known(v___x_274_, 1);
v___y_266_ = v___y_273_;
v_i_267_ = v_index_278_;
goto v___jp_265_;
}
default: 
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_273_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_index_281_; 
v_index_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_281_);
lean_dec_ref_known(v___x_280_, 1);
v___y_266_ = v___y_273_;
v_i_267_ = v_index_281_;
goto v___jp_265_;
}
else
{
v___y_258_ = v___y_273_;
goto v___jp_257_;
}
}
}
}
v___jp_282_:
{
lean_object* v_size_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_size_285_ = lean_ctor_get(v___y_283_, 0);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_size_285_, v___x_286_);
lean_inc_ref(v_decl_221_);
v___x_288_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_283_, v___x_287_, v_i_284_, v_decl_221_, v_g_256_);
lean_dec(v_i_284_);
v___y_258_ = v___x_288_;
goto v___jp_257_;
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(v_cache_205_);
lean_dec_ref(v_cache_205_);
lean_inc_ref(v_decl_221_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v___x_290_, v_decl_221_);
switch(lean_obj_tag(v___x_291_))
{
case 0:
{
lean_object* v_index_292_; lean_object* v_size_293_; lean_object* v___x_294_; 
v_index_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_292_);
lean_dec_ref_known(v___x_291_, 3);
v_size_293_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_size_293_);
lean_inc_ref(v_decl_221_);
v___x_294_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_290_, v_size_293_, v_index_292_, v_decl_221_, v_g_256_);
lean_dec(v_index_292_);
v___y_258_ = v___x_294_;
goto v___jp_257_;
}
case 1:
{
lean_object* v_index_295_; 
v_index_295_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_295_);
lean_dec_ref_known(v___x_291_, 1);
v___y_283_ = v___x_290_;
v_i_284_ = v_index_295_;
goto v___jp_282_;
}
default: 
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_290_, v___x_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_index_298_; 
v_index_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_298_);
lean_dec_ref_known(v___x_297_, 1);
v___y_283_ = v___x_290_;
v_i_284_ = v_index_298_;
goto v___jp_282_;
}
else
{
v___y_258_ = v___x_290_;
goto v___jp_257_;
}
}
}
}
}
else
{
lean_del_object(v___x_243_);
lean_dec_ref(v_decl_221_);
lean_dec_ref(v_cache_205_);
lean_dec_ref(v_decls_204_);
if (v_invert_210_ == 0)
{
if (v_invert_212_ == 0)
{
v___y_231_ = v___x_255_;
goto v___jp_230_;
}
else
{
lean_dec(v_gate_209_);
v___y_226_ = v_invert_210_;
goto v___jp_225_;
}
}
else
{
v___y_231_ = v_invert_212_;
goto v___jp_230_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v_decl_221_);
lean_dec(v_gate_209_);
lean_dec_ref(v_lhs_199_);
v_isSharedCheck_344_ = !lean_is_exclusive(v_rhs_200_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_rhs_200_, 0);
lean_dec(v_unused_345_);
v___x_333_ = v_rhs_200_;
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
else
{
lean_dec(v_rhs_200_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_val_335_; lean_object* v___x_337_; 
v_val_335_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_222_, 1);
if (v_isShared_208_ == 0)
{
v___x_337_ = v___x_207_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_decls_204_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_cache_205_);
v___x_337_ = v_reuseFailAlloc_343_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
uint8_t v___x_338_; lean_object* v___x_340_; 
v___x_338_ = 0;
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_val_335_);
v___x_340_ = v___x_333_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_val_335_);
v___x_340_ = v_reuseFailAlloc_342_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; 
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_338_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_337_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
return v___x_341_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object* v_aig_349_, lean_object* v_input_350_){
_start:
{
lean_object* v_lhs_351_; lean_object* v_rhs_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_367_; 
v_lhs_351_ = lean_ctor_get(v_input_350_, 0);
v_rhs_352_ = lean_ctor_get(v_input_350_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_input_350_);
if (v_isSharedCheck_367_ == 0)
{
v___x_354_ = v_input_350_;
v_isShared_355_ = v_isSharedCheck_367_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_rhs_352_);
lean_inc(v_lhs_351_);
lean_dec(v_input_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_367_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_gate_356_; lean_object* v_gate_357_; uint8_t v___x_358_; 
v_gate_356_ = lean_ctor_get(v_lhs_351_, 0);
v_gate_357_ = lean_ctor_get(v_rhs_352_, 0);
v___x_358_ = lean_nat_dec_lt(v_gate_356_, v_gate_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_lhs_351_);
lean_ctor_set(v___x_354_, 0, v_rhs_352_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_rhs_352_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_lhs_351_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_349_, v___x_360_);
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
if (v_isShared_355_ == 0)
{
v___x_364_ = v___x_354_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_lhs_351_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_rhs_352_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_349_, v___x_364_);
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object* v_aig_368_, lean_object* v_input_369_){
_start:
{
lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v_lhs_431_; lean_object* v_rhs_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_476_; 
v_lhs_431_ = lean_ctor_get(v_input_369_, 0);
v_rhs_432_ = lean_ctor_get(v_input_369_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_input_369_);
if (v_isSharedCheck_476_ == 0)
{
v___x_434_ = v_input_369_;
v_isShared_435_ = v_isSharedCheck_476_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_rhs_432_);
lean_inc(v_lhs_431_);
lean_dec(v_input_369_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_476_;
goto v_resetjp_433_;
}
v___jp_370_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___y_372_);
lean_ctor_set(v___x_374_, 1, v___y_373_);
v___x_375_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_371_, v___x_374_);
return v___x_375_;
}
v___jp_376_:
{
uint8_t v_invert_380_; 
v_invert_380_ = lean_ctor_get_uint8(v___y_377_, sizeof(void*)*1);
if (v_invert_380_ == 0)
{
lean_object* v_gate_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_gate_381_ = lean_ctor_get(v___y_377_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___y_377_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v___y_377_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_gate_381_);
lean_dec(v___y_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; lean_object* v___x_387_; 
v___x_385_ = 1;
if (v_isShared_384_ == 0)
{
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_gate_381_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_385_);
v___y_371_ = v___y_378_;
v___y_372_ = v___y_379_;
v___y_373_ = v___x_387_;
goto v___jp_370_;
}
}
}
else
{
lean_object* v_gate_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_gate_390_ = lean_ctor_get(v___y_377_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___y_377_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v___y_377_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_gate_390_);
lean_dec(v___y_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; lean_object* v___x_396_; 
v___x_394_ = 0;
if (v_isShared_393_ == 0)
{
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_gate_390_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*1, v___x_394_);
v___y_371_ = v___y_378_;
v___y_372_ = v___y_379_;
v___y_373_ = v___x_396_;
goto v___jp_370_;
}
}
}
}
v___jp_399_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_res_407_; uint8_t v_invert_408_; 
v___x_405_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_405_, 0, v___y_403_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*1, v___y_402_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___y_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v_res_407_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_401_, v___x_406_);
v_invert_408_ = lean_ctor_get_uint8(v___y_400_, sizeof(void*)*1);
if (v_invert_408_ == 0)
{
lean_object* v_aig_409_; lean_object* v_ref_410_; lean_object* v_gate_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_aig_409_ = lean_ctor_get(v_res_407_, 0);
lean_inc_ref(v_aig_409_);
v_ref_410_ = lean_ctor_get(v_res_407_, 1);
lean_inc_ref(v_ref_410_);
lean_dec_ref(v_res_407_);
v_gate_411_ = lean_ctor_get(v___y_400_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___y_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v___y_400_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_gate_411_);
lean_dec(v___y_400_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
uint8_t v___x_415_; lean_object* v___x_417_; 
v___x_415_ = 1;
if (v_isShared_414_ == 0)
{
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_gate_411_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_415_);
v___y_377_ = v_ref_410_;
v___y_378_ = v_aig_409_;
v___y_379_ = v___x_417_;
goto v___jp_376_;
}
}
}
else
{
lean_object* v_aig_420_; lean_object* v_ref_421_; lean_object* v_gate_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_aig_420_ = lean_ctor_get(v_res_407_, 0);
lean_inc_ref(v_aig_420_);
v_ref_421_ = lean_ctor_get(v_res_407_, 1);
lean_inc_ref(v_ref_421_);
lean_dec_ref(v_res_407_);
v_gate_422_ = lean_ctor_get(v___y_400_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___y_400_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___y_400_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_gate_422_);
lean_dec(v___y_400_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint8_t v___x_426_; lean_object* v___x_428_; 
v___x_426_ = 0;
if (v_isShared_425_ == 0)
{
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_gate_422_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_426_);
v___y_377_ = v_ref_421_;
v___y_378_ = v_aig_420_;
v___y_379_ = v___x_428_;
goto v___jp_376_;
}
}
}
}
v_resetjp_433_:
{
lean_object* v_gate_436_; uint8_t v_invert_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_475_; 
v_gate_436_ = lean_ctor_get(v_lhs_431_, 0);
v_invert_437_ = lean_ctor_get_uint8(v_lhs_431_, sizeof(void*)*1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_lhs_431_);
if (v_isSharedCheck_475_ == 0)
{
v___x_439_ = v_lhs_431_;
v_isShared_440_ = v_isSharedCheck_475_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_gate_436_);
lean_dec(v_lhs_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_475_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_gate_441_; uint8_t v_invert_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_474_; 
v_gate_441_ = lean_ctor_get(v_rhs_432_, 0);
v_invert_442_ = lean_ctor_get_uint8(v_rhs_432_, sizeof(void*)*1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_rhs_432_);
if (v_isSharedCheck_474_ == 0)
{
v___x_444_ = v_rhs_432_;
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_gate_441_);
lean_dec(v_rhs_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___y_447_; lean_object* v___x_462_; 
lean_inc(v_gate_436_);
if (v_isShared_440_ == 0)
{
v___x_462_ = v___x_439_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_gate_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*1, v_invert_437_);
v___x_462_ = v_reuseFailAlloc_473_;
goto v_reusejp_461_;
}
v___jp_446_:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_368_, v___y_447_);
if (v_invert_437_ == 0)
{
lean_object* v_aig_449_; lean_object* v_ref_450_; uint8_t v___x_451_; lean_object* v___x_453_; 
v_aig_449_ = lean_ctor_get(v_res_448_, 0);
lean_inc_ref(v_aig_449_);
v_ref_450_ = lean_ctor_get(v_res_448_, 1);
lean_inc_ref(v_ref_450_);
lean_dec_ref(v_res_448_);
v___x_451_ = 1;
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_gate_436_);
v___x_453_ = v___x_444_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_gate_436_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___x_451_);
v___y_400_ = v_ref_450_;
v___y_401_ = v_aig_449_;
v___y_402_ = v_invert_442_;
v___y_403_ = v_gate_441_;
v___y_404_ = v___x_453_;
goto v___jp_399_;
}
}
else
{
lean_object* v_aig_455_; lean_object* v_ref_456_; uint8_t v___x_457_; lean_object* v___x_459_; 
v_aig_455_ = lean_ctor_get(v_res_448_, 0);
lean_inc_ref(v_aig_455_);
v_ref_456_ = lean_ctor_get(v_res_448_, 1);
lean_inc_ref(v_ref_456_);
lean_dec_ref(v_res_448_);
v___x_457_ = 0;
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_gate_436_);
v___x_459_ = v___x_444_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_gate_436_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*1, v___x_457_);
v___y_400_ = v_ref_456_;
v___y_401_ = v_aig_455_;
v___y_402_ = v_invert_442_;
v___y_403_ = v_gate_441_;
v___y_404_ = v___x_459_;
goto v___jp_399_;
}
}
}
v_reusejp_461_:
{
if (v_invert_442_ == 0)
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = 1;
lean_inc(v_gate_441_);
v___x_464_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_464_, 0, v_gate_441_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*1, v___x_463_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_464_);
lean_ctor_set(v___x_434_, 0, v___x_462_);
v___x_466_ = v___x_434_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v___y_447_ = v___x_466_;
goto v___jp_446_;
}
}
else
{
uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = 0;
lean_inc(v_gate_441_);
v___x_469_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_469_, 0, v_gate_441_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*1, v___x_468_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_469_);
lean_ctor_set(v___x_434_, 0, v___x_462_);
v___x_471_ = v___x_434_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v___y_447_ = v___x_471_;
goto v___jp_446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* v_aig_477_, lean_object* v_input_478_){
_start:
{
lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v_res_508_; lean_object* v_aig_509_; lean_object* v_ref_510_; lean_object* v___y_512_; lean_object* v_lhs_537_; lean_object* v_rhs_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_578_; 
lean_inc_ref(v_input_478_);
v_res_508_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_477_, v_input_478_);
v_aig_509_ = lean_ctor_get(v_res_508_, 0);
lean_inc_ref(v_aig_509_);
v_ref_510_ = lean_ctor_get(v_res_508_, 1);
lean_inc_ref(v_ref_510_);
lean_dec_ref(v_res_508_);
v_lhs_537_ = lean_ctor_get(v_input_478_, 0);
v_rhs_538_ = lean_ctor_get(v_input_478_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_input_478_);
if (v_isSharedCheck_578_ == 0)
{
v___x_540_ = v_input_478_;
v_isShared_541_ = v_isSharedCheck_578_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_rhs_538_);
lean_inc(v_lhs_537_);
lean_dec(v_input_478_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_578_;
goto v_resetjp_539_;
}
v___jp_479_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___y_480_);
lean_ctor_set(v___x_483_, 1, v___y_482_);
v___x_484_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_481_, v___x_483_);
return v___x_484_;
}
v___jp_485_:
{
uint8_t v_invert_489_; 
v_invert_489_ = lean_ctor_get_uint8(v___y_486_, sizeof(void*)*1);
if (v_invert_489_ == 0)
{
lean_object* v_gate_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_gate_490_ = lean_ctor_get(v___y_486_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___y_486_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v___y_486_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_gate_490_);
lean_dec(v___y_486_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint8_t v___x_494_; lean_object* v___x_496_; 
v___x_494_ = 1;
if (v_isShared_493_ == 0)
{
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_gate_490_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_494_);
v___y_480_ = v___y_488_;
v___y_481_ = v___y_487_;
v___y_482_ = v___x_496_;
goto v___jp_479_;
}
}
}
else
{
lean_object* v_gate_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_gate_499_ = lean_ctor_get(v___y_486_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___y_486_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___y_486_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_gate_499_);
lean_dec(v___y_486_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___x_503_; lean_object* v___x_505_; 
v___x_503_ = 0;
if (v_isShared_502_ == 0)
{
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_gate_499_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*1, v___x_503_);
v___y_480_ = v___y_488_;
v___y_481_ = v___y_487_;
v___y_482_ = v___x_505_;
goto v___jp_479_;
}
}
}
}
v___jp_511_:
{
lean_object* v_res_513_; uint8_t v_invert_514_; 
v_res_513_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_509_, v___y_512_);
v_invert_514_ = lean_ctor_get_uint8(v_ref_510_, sizeof(void*)*1);
if (v_invert_514_ == 0)
{
lean_object* v_aig_515_; lean_object* v_ref_516_; lean_object* v_gate_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_aig_515_ = lean_ctor_get(v_res_513_, 0);
lean_inc_ref(v_aig_515_);
v_ref_516_ = lean_ctor_get(v_res_513_, 1);
lean_inc_ref(v_ref_516_);
lean_dec_ref(v_res_513_);
v_gate_517_ = lean_ctor_get(v_ref_510_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_ref_510_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_ref_510_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_gate_517_);
lean_dec(v_ref_510_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; lean_object* v___x_523_; 
v___x_521_ = 1;
if (v_isShared_520_ == 0)
{
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_gate_517_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_521_);
v___y_486_ = v_ref_516_;
v___y_487_ = v_aig_515_;
v___y_488_ = v___x_523_;
goto v___jp_485_;
}
}
}
else
{
lean_object* v_aig_526_; lean_object* v_ref_527_; lean_object* v_gate_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_aig_526_ = lean_ctor_get(v_res_513_, 0);
lean_inc_ref(v_aig_526_);
v_ref_527_ = lean_ctor_get(v_res_513_, 1);
lean_inc_ref(v_ref_527_);
lean_dec_ref(v_res_513_);
v_gate_528_ = lean_ctor_get(v_ref_510_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_ref_510_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_ref_510_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_gate_528_);
lean_dec(v_ref_510_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v___x_532_; lean_object* v___x_534_; 
v___x_532_ = 0;
if (v_isShared_531_ == 0)
{
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_gate_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_532_);
v___y_486_ = v_ref_527_;
v___y_487_ = v_aig_526_;
v___y_488_ = v___x_534_;
goto v___jp_485_;
}
}
}
}
v_resetjp_539_:
{
lean_object* v_gate_542_; uint8_t v_invert_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_577_; 
v_gate_542_ = lean_ctor_get(v_lhs_537_, 0);
v_invert_543_ = lean_ctor_get_uint8(v_lhs_537_, sizeof(void*)*1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_lhs_537_);
if (v_isSharedCheck_577_ == 0)
{
v___x_545_ = v_lhs_537_;
v_isShared_546_ = v_isSharedCheck_577_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_gate_542_);
lean_dec(v_lhs_537_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_577_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_gate_547_; uint8_t v_invert_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_576_; 
v_gate_547_ = lean_ctor_get(v_rhs_538_, 0);
v_invert_548_ = lean_ctor_get_uint8(v_rhs_538_, sizeof(void*)*1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_rhs_538_);
if (v_isSharedCheck_576_ == 0)
{
v___x_550_ = v_rhs_538_;
v_isShared_551_ = v_isSharedCheck_576_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_gate_547_);
lean_dec(v_rhs_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_576_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___y_553_; 
if (v_invert_543_ == 0)
{
uint8_t v___x_568_; lean_object* v___x_570_; 
v___x_568_ = 1;
if (v_isShared_546_ == 0)
{
v___x_570_ = v___x_545_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_gate_542_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*1, v___x_568_);
v___y_553_ = v___x_570_;
goto v___jp_552_;
}
}
else
{
uint8_t v___x_572_; lean_object* v___x_574_; 
v___x_572_ = 0;
if (v_isShared_546_ == 0)
{
v___x_574_ = v___x_545_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_gate_542_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_572_);
v___y_553_ = v___x_574_;
goto v___jp_552_;
}
}
v___jp_552_:
{
if (v_invert_548_ == 0)
{
uint8_t v___x_554_; lean_object* v___x_556_; 
v___x_554_ = 1;
if (v_isShared_551_ == 0)
{
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_gate_547_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_554_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_556_);
lean_ctor_set(v___x_540_, 0, v___y_553_);
v___x_558_ = v___x_540_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___y_553_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v___y_512_ = v___x_558_;
goto v___jp_511_;
}
}
}
else
{
uint8_t v___x_561_; lean_object* v___x_563_; 
v___x_561_ = 0;
if (v_isShared_551_ == 0)
{
v___x_563_ = v___x_550_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_gate_547_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*1, v___x_561_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_563_);
lean_ctor_set(v___x_540_, 0, v___y_553_);
v___x_565_ = v___x_540_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___y_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v___y_512_ = v___x_565_;
goto v___jp_511_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* v_aig_579_, lean_object* v_input_580_){
_start:
{
lean_object* v___y_582_; lean_object* v_lhs_622_; lean_object* v_rhs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_673_; 
v_lhs_622_ = lean_ctor_get(v_input_580_, 0);
v_rhs_623_ = lean_ctor_get(v_input_580_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_input_580_);
if (v_isSharedCheck_673_ == 0)
{
v___x_625_ = v_input_580_;
v_isShared_626_ = v_isSharedCheck_673_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_rhs_623_);
lean_inc(v_lhs_622_);
lean_dec(v_input_580_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_673_;
goto v_resetjp_624_;
}
v___jp_581_:
{
lean_object* v_res_583_; lean_object* v_ref_584_; uint8_t v_invert_585_; 
v_res_583_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_579_, v___y_582_);
v_ref_584_ = lean_ctor_get(v_res_583_, 1);
lean_inc_ref(v_ref_584_);
v_invert_585_ = lean_ctor_get_uint8(v_ref_584_, sizeof(void*)*1);
if (v_invert_585_ == 0)
{
lean_object* v_aig_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_602_; 
v_aig_586_ = lean_ctor_get(v_res_583_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_res_583_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_res_583_, 1);
lean_dec(v_unused_603_);
v___x_588_ = v_res_583_;
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_aig_586_);
lean_dec(v_res_583_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_gate_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_601_; 
v_gate_590_ = lean_ctor_get(v_ref_584_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_ref_584_);
if (v_isSharedCheck_601_ == 0)
{
v___x_592_ = v_ref_584_;
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_gate_590_);
lean_dec(v_ref_584_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_594_; lean_object* v___x_596_; 
v___x_594_ = 1;
if (v_isShared_593_ == 0)
{
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_gate_590_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*1, v___x_594_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_596_);
v___x_598_ = v___x_588_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_aig_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_aig_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_620_; 
v_aig_604_ = lean_ctor_get(v_res_583_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_res_583_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_res_583_, 1);
lean_dec(v_unused_621_);
v___x_606_ = v_res_583_;
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_aig_604_);
lean_dec(v_res_583_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_gate_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_619_; 
v_gate_608_ = lean_ctor_get(v_ref_584_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_ref_584_);
if (v_isSharedCheck_619_ == 0)
{
v___x_610_ = v_ref_584_;
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_gate_608_);
lean_dec(v_ref_584_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint8_t v___x_612_; lean_object* v___x_614_; 
v___x_612_ = 0;
if (v_isShared_611_ == 0)
{
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_gate_608_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v___x_612_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_614_);
v___x_616_ = v___x_606_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_aig_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
v_resetjp_624_:
{
lean_object* v___y_628_; uint8_t v_invert_654_; 
v_invert_654_ = lean_ctor_get_uint8(v_lhs_622_, sizeof(void*)*1);
if (v_invert_654_ == 0)
{
lean_object* v_gate_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_gate_655_ = lean_ctor_get(v_lhs_622_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_lhs_622_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v_lhs_622_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_gate_655_);
lean_dec(v_lhs_622_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; lean_object* v___x_661_; 
v___x_659_ = 1;
if (v_isShared_658_ == 0)
{
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_gate_655_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*1, v___x_659_);
v___y_628_ = v___x_661_;
goto v___jp_627_;
}
}
}
else
{
lean_object* v_gate_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_gate_664_ = lean_ctor_get(v_lhs_622_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_lhs_622_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_lhs_622_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_gate_664_);
lean_dec(v_lhs_622_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
uint8_t v___x_668_; lean_object* v___x_670_; 
v___x_668_ = 0;
if (v_isShared_667_ == 0)
{
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_gate_664_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_668_);
v___y_628_ = v___x_670_;
goto v___jp_627_;
}
}
}
v___jp_627_:
{
uint8_t v_invert_629_; 
v_invert_629_ = lean_ctor_get_uint8(v_rhs_623_, sizeof(void*)*1);
if (v_invert_629_ == 0)
{
lean_object* v_gate_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_641_; 
v_gate_630_ = lean_ctor_get(v_rhs_623_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_rhs_623_);
if (v_isSharedCheck_641_ == 0)
{
v___x_632_ = v_rhs_623_;
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_gate_630_);
lean_dec(v_rhs_623_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
uint8_t v___x_634_; lean_object* v___x_636_; 
v___x_634_ = 1;
if (v_isShared_633_ == 0)
{
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_gate_630_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*1, v___x_634_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_636_);
lean_ctor_set(v___x_625_, 0, v___y_628_);
v___x_638_ = v___x_625_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___y_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v___y_582_ = v___x_638_;
goto v___jp_581_;
}
}
}
}
else
{
lean_object* v_gate_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_gate_642_ = lean_ctor_get(v_rhs_623_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_rhs_623_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v_rhs_623_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_gate_642_);
lean_dec(v_rhs_623_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; lean_object* v___x_648_; 
v___x_646_ = 0;
if (v_isShared_645_ == 0)
{
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_gate_642_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v___x_646_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_648_);
lean_ctor_set(v___x_625_, 0, v___y_628_);
v___x_650_ = v___x_625_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___y_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_582_ = v___x_650_;
goto v___jp_581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* v_aig_674_, lean_object* v_input_675_){
_start:
{
lean_object* v_discr_676_; lean_object* v_lhs_677_; lean_object* v_rhs_678_; lean_object* v___x_679_; lean_object* v_res_680_; lean_object* v_aig_681_; lean_object* v_ref_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_735_; 
v_discr_676_ = lean_ctor_get(v_input_675_, 0);
lean_inc_ref_n(v_discr_676_, 2);
v_lhs_677_ = lean_ctor_get(v_input_675_, 1);
lean_inc_ref(v_lhs_677_);
v_rhs_678_ = lean_ctor_get(v_input_675_, 2);
lean_inc_ref(v_rhs_678_);
lean_dec_ref(v_input_675_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_discr_676_);
lean_ctor_set(v___x_679_, 1, v_lhs_677_);
v_res_680_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_674_, v___x_679_);
v_aig_681_ = lean_ctor_get(v_res_680_, 0);
v_ref_682_ = lean_ctor_get(v_res_680_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_res_680_);
if (v_isSharedCheck_735_ == 0)
{
v___x_684_ = v_res_680_;
v_isShared_685_ = v_isSharedCheck_735_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_ref_682_);
lean_inc(v_aig_681_);
lean_dec(v_res_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_735_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_gate_686_; uint8_t v_invert_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_734_; 
v_gate_686_ = lean_ctor_get(v_discr_676_, 0);
v_invert_687_ = lean_ctor_get_uint8(v_discr_676_, sizeof(void*)*1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_discr_676_);
if (v_isSharedCheck_734_ == 0)
{
v___x_689_ = v_discr_676_;
v_isShared_690_ = v_isSharedCheck_734_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_gate_686_);
lean_dec(v_discr_676_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_734_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_gate_691_; uint8_t v_invert_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_733_; 
v_gate_691_ = lean_ctor_get(v_rhs_678_, 0);
v_invert_692_ = lean_ctor_get_uint8(v_rhs_678_, sizeof(void*)*1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_rhs_678_);
if (v_isSharedCheck_733_ == 0)
{
v___x_694_ = v_rhs_678_;
v_isShared_695_ = v_isSharedCheck_733_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_gate_691_);
lean_dec(v_rhs_678_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_733_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_aig_697_; lean_object* v_ref_698_; 
if (v_invert_687_ == 0)
{
uint8_t v___x_725_; lean_object* v___x_727_; 
v___x_725_ = 1;
if (v_isShared_690_ == 0)
{
v___x_727_ = v___x_689_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_gate_686_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*1, v___x_725_);
v_aig_697_ = v_aig_681_;
v_ref_698_ = v___x_727_;
goto v___jp_696_;
}
}
else
{
uint8_t v___x_729_; lean_object* v___x_731_; 
v___x_729_ = 0;
if (v_isShared_690_ == 0)
{
v___x_731_ = v___x_689_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_gate_686_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_729_);
v_aig_697_ = v_aig_681_;
v_ref_698_ = v___x_731_;
goto v___jp_696_;
}
}
v___jp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_695_ == 0)
{
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_gate_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*1, v_invert_692_);
v___x_700_ = v_reuseFailAlloc_724_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_700_);
lean_ctor_set(v___x_684_, 0, v_ref_698_);
v___x_702_ = v___x_684_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_ref_698_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_723_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v_res_703_; lean_object* v_aig_704_; lean_object* v_ref_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_722_; 
v_res_703_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_697_, v___x_702_);
v_aig_704_ = lean_ctor_get(v_res_703_, 0);
v_ref_705_ = lean_ctor_get(v_res_703_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_res_703_);
if (v_isSharedCheck_722_ == 0)
{
v___x_707_ = v_res_703_;
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_ref_705_);
lean_inc(v_aig_704_);
lean_dec(v_res_703_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_gate_709_; uint8_t v_invert_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_gate_709_ = lean_ctor_get(v_ref_682_, 0);
v_invert_710_ = lean_ctor_get_uint8(v_ref_682_, sizeof(void*)*1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_ref_682_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v_ref_682_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_gate_709_);
lean_dec(v_ref_682_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_lhsRef_715_; 
if (v_isShared_713_ == 0)
{
v_lhsRef_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_gate_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*1, v_invert_710_);
v_lhsRef_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_lhsRef_715_);
v___x_717_ = v___x_707_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_lhsRef_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_ref_705_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_704_, v___x_717_);
return v___x_718_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* v_aig_736_, lean_object* v_expr_737_, lean_object* v_cache_738_){
_start:
{
switch(lean_obj_tag(v_expr_737_))
{
case 0:
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v_expr_737_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v_expr_737_, 1);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_a_739_);
lean_ctor_set(v___x_740_, 1, v_cache_738_);
v___x_741_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_736_, v___x_740_);
return v___x_741_;
}
case 1:
{
uint8_t v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_742_ = lean_ctor_get_uint8(v_expr_737_, 0);
lean_dec_ref_known(v_expr_737_, 0);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v_a_742_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_aig_736_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_cache_738_);
return v___x_746_;
}
case 2:
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v_result_749_; lean_object* v_ref_750_; uint8_t v_invert_751_; 
v_a_747_ = lean_ctor_get(v_expr_737_, 0);
lean_inc_ref(v_a_747_);
lean_dec_ref_known(v_expr_737_, 1);
v___x_748_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_736_, v_a_747_, v_cache_738_);
v_result_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_result_749_);
v_ref_750_ = lean_ctor_get(v_result_749_, 1);
lean_inc_ref(v_ref_750_);
v_invert_751_ = lean_ctor_get_uint8(v_ref_750_, sizeof(void*)*1);
if (v_invert_751_ == 0)
{
lean_object* v_cache_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_777_; 
v_cache_752_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_748_, 0);
lean_dec(v_unused_778_);
v___x_754_ = v___x_748_;
v_isShared_755_ = v_isSharedCheck_777_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_cache_752_);
lean_dec(v___x_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_777_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_aig_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_775_; 
v_aig_756_ = lean_ctor_get(v_result_749_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_result_749_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_result_749_, 1);
lean_dec(v_unused_776_);
v___x_758_ = v_result_749_;
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_aig_756_);
lean_dec(v_result_749_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_775_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_gate_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_774_; 
v_gate_760_ = lean_ctor_get(v_ref_750_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_ref_750_);
if (v_isSharedCheck_774_ == 0)
{
v___x_762_ = v_ref_750_;
v_isShared_763_ = v_isSharedCheck_774_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_gate_760_);
lean_dec(v_ref_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_774_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; lean_object* v___x_766_; 
v___x_764_ = 1;
if (v_isShared_763_ == 0)
{
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_gate_760_);
v___x_766_ = v_reuseFailAlloc_773_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*1, v___x_764_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_766_);
v___x_768_ = v___x_758_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_aig_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_768_);
v___x_770_ = v___x_754_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_cache_752_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
else
{
lean_object* v_cache_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_804_; 
v_cache_779_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_748_, 0);
lean_dec(v_unused_805_);
v___x_781_ = v___x_748_;
v_isShared_782_ = v_isSharedCheck_804_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_cache_779_);
lean_dec(v___x_748_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_804_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_aig_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_802_; 
v_aig_783_ = lean_ctor_get(v_result_749_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_result_749_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_result_749_, 1);
lean_dec(v_unused_803_);
v___x_785_ = v_result_749_;
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_aig_783_);
lean_dec(v_result_749_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_gate_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_801_; 
v_gate_787_ = lean_ctor_get(v_ref_750_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_ref_750_);
if (v_isSharedCheck_801_ == 0)
{
v___x_789_ = v_ref_750_;
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_gate_787_);
lean_dec(v_ref_750_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; lean_object* v___x_793_; 
v___x_791_ = 0;
if (v_isShared_790_ == 0)
{
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_gate_787_);
v___x_793_ = v_reuseFailAlloc_800_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*1, v___x_791_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_793_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_aig_783_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_795_);
v___x_797_ = v___x_781_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_cache_779_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
}
}
case 3:
{
uint8_t v_a_806_; lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v_result_810_; lean_object* v_cache_811_; lean_object* v_aig_812_; lean_object* v_ref_813_; lean_object* v___x_814_; lean_object* v_result_815_; lean_object* v_cache_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_854_; 
v_a_806_ = lean_ctor_get_uint8(v_expr_737_, sizeof(void*)*2);
v_a_807_ = lean_ctor_get(v_expr_737_, 0);
lean_inc_ref(v_a_807_);
v_a_808_ = lean_ctor_get(v_expr_737_, 1);
lean_inc_ref(v_a_808_);
lean_dec_ref_known(v_expr_737_, 2);
v___x_809_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_736_, v_a_807_, v_cache_738_);
v_result_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_result_810_);
v_cache_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref(v_cache_811_);
lean_dec_ref(v___x_809_);
v_aig_812_ = lean_ctor_get(v_result_810_, 0);
lean_inc_ref(v_aig_812_);
v_ref_813_ = lean_ctor_get(v_result_810_, 1);
lean_inc_ref(v_ref_813_);
lean_dec_ref(v_result_810_);
v___x_814_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_812_, v_a_808_, v_cache_811_);
v_result_815_ = lean_ctor_get(v___x_814_, 0);
v_cache_816_ = lean_ctor_get(v___x_814_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_854_ == 0)
{
v___x_818_ = v___x_814_;
v_isShared_819_ = v_isSharedCheck_854_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_cache_816_);
lean_inc(v_result_815_);
lean_dec(v___x_814_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_854_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_aig_820_; lean_object* v_ref_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_853_; 
v_aig_820_ = lean_ctor_get(v_result_815_, 0);
v_ref_821_ = lean_ctor_get(v_result_815_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_result_815_);
if (v_isSharedCheck_853_ == 0)
{
v___x_823_ = v_result_815_;
v_isShared_824_ = v_isSharedCheck_853_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_ref_821_);
lean_inc(v_aig_820_);
lean_dec(v_result_815_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_853_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_gate_825_; uint8_t v_invert_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_852_; 
v_gate_825_ = lean_ctor_get(v_ref_813_, 0);
v_invert_826_ = lean_ctor_get_uint8(v_ref_813_, sizeof(void*)*1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_ref_813_);
if (v_isSharedCheck_852_ == 0)
{
v___x_828_ = v_ref_813_;
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_gate_825_);
lean_dec(v_ref_813_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_lhsRef_831_; 
if (v_isShared_829_ == 0)
{
v_lhsRef_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_gate_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*1, v_invert_826_);
v_lhsRef_831_ = v_reuseFailAlloc_851_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v_input_833_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_lhsRef_831_);
v_input_833_ = v___x_823_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_lhsRef_831_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_ref_821_);
v_input_833_ = v_reuseFailAlloc_850_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
switch(v_a_806_)
{
case 0:
{
lean_object* v_ret_834_; lean_object* v___x_836_; 
v_ret_834_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_820_, v_input_833_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_ret_834_);
v___x_836_ = v___x_818_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_ret_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_cache_816_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
case 1:
{
lean_object* v_ret_838_; lean_object* v___x_840_; 
v_ret_838_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_820_, v_input_833_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_ret_838_);
v___x_840_ = v___x_818_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_ret_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_cache_816_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
case 2:
{
lean_object* v_ret_842_; lean_object* v___x_844_; 
v_ret_842_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_820_, v_input_833_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_ret_842_);
v___x_844_ = v___x_818_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_ret_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_cache_816_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
default: 
{
lean_object* v_ret_846_; lean_object* v___x_848_; 
v_ret_846_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_820_, v_input_833_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_ret_846_);
v___x_848_ = v___x_818_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_ret_846_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_cache_816_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_a_855_; lean_object* v_a_856_; lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_905_; 
v_a_855_ = lean_ctor_get(v_expr_737_, 0);
v_a_856_ = lean_ctor_get(v_expr_737_, 1);
v_a_857_ = lean_ctor_get(v_expr_737_, 2);
v_isSharedCheck_905_ = !lean_is_exclusive(v_expr_737_);
if (v_isSharedCheck_905_ == 0)
{
v___x_859_ = v_expr_737_;
v_isShared_860_ = v_isSharedCheck_905_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_inc(v_a_856_);
lean_inc(v_a_855_);
lean_dec(v_expr_737_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_905_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v_result_862_; lean_object* v_cache_863_; lean_object* v_aig_864_; lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v_result_867_; lean_object* v_cache_868_; lean_object* v_aig_869_; lean_object* v_ref_870_; lean_object* v___x_871_; lean_object* v_result_872_; lean_object* v_cache_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_904_; 
v___x_861_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_736_, v_a_855_, v_cache_738_);
v_result_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_result_862_);
v_cache_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc_ref(v_cache_863_);
lean_dec_ref(v___x_861_);
v_aig_864_ = lean_ctor_get(v_result_862_, 0);
lean_inc_ref(v_aig_864_);
v_ref_865_ = lean_ctor_get(v_result_862_, 1);
lean_inc_ref(v_ref_865_);
lean_dec_ref(v_result_862_);
v___x_866_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_864_, v_a_856_, v_cache_863_);
v_result_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_result_867_);
v_cache_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc_ref(v_cache_868_);
lean_dec_ref(v___x_866_);
v_aig_869_ = lean_ctor_get(v_result_867_, 0);
lean_inc_ref(v_aig_869_);
v_ref_870_ = lean_ctor_get(v_result_867_, 1);
lean_inc_ref(v_ref_870_);
lean_dec_ref(v_result_867_);
v___x_871_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_869_, v_a_857_, v_cache_868_);
v_result_872_ = lean_ctor_get(v___x_871_, 0);
v_cache_873_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_904_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_904_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_cache_873_);
lean_inc(v_result_872_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_904_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_aig_877_; lean_object* v_ref_878_; lean_object* v_gate_879_; uint8_t v_invert_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_903_; 
v_aig_877_ = lean_ctor_get(v_result_872_, 0);
lean_inc_ref(v_aig_877_);
v_ref_878_ = lean_ctor_get(v_result_872_, 1);
lean_inc_ref(v_ref_878_);
lean_dec_ref(v_result_872_);
v_gate_879_ = lean_ctor_get(v_ref_865_, 0);
v_invert_880_ = lean_ctor_get_uint8(v_ref_865_, sizeof(void*)*1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_ref_865_);
if (v_isSharedCheck_903_ == 0)
{
v___x_882_ = v_ref_865_;
v_isShared_883_ = v_isSharedCheck_903_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_gate_879_);
lean_dec(v_ref_865_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_903_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_gate_884_; uint8_t v_invert_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_902_; 
v_gate_884_ = lean_ctor_get(v_ref_870_, 0);
v_invert_885_ = lean_ctor_get_uint8(v_ref_870_, sizeof(void*)*1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_ref_870_);
if (v_isSharedCheck_902_ == 0)
{
v___x_887_ = v_ref_870_;
v_isShared_888_ = v_isSharedCheck_902_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_gate_884_);
lean_dec(v_ref_870_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_902_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_discrRef_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_gate_879_);
v_discrRef_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_gate_879_);
v_discrRef_890_ = v_reuseFailAlloc_901_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v_lhsRef_892_; 
lean_ctor_set_uint8(v_discrRef_890_, sizeof(void*)*1, v_invert_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_gate_884_);
v_lhsRef_892_ = v___x_882_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_gate_884_);
v_lhsRef_892_ = v_reuseFailAlloc_900_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v_input_894_; 
lean_ctor_set_uint8(v_lhsRef_892_, sizeof(void*)*1, v_invert_885_);
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 0);
lean_ctor_set(v___x_859_, 2, v_ref_878_);
lean_ctor_set(v___x_859_, 1, v_lhsRef_892_);
lean_ctor_set(v___x_859_, 0, v_discrRef_890_);
v_input_894_ = v___x_859_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_discrRef_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_lhsRef_892_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_ref_878_);
v_input_894_ = v_reuseFailAlloc_899_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v_ret_895_; lean_object* v___x_897_; 
v_ret_895_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_877_, v_input_894_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_ret_895_);
v___x_897_ = v___x_875_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_ret_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_cache_873_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_907_, v_a_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_910_, v_m_911_, v_a_912_);
lean_dec_ref(v_m_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_914_, lean_object* v_m_915_, lean_object* v_query_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_915_, v_query_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_query_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(v_00_u03b2_918_, v_m_919_, v_query_920_);
lean_dec_ref(v_m_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_922_, lean_object* v_m_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___redArg(v_m_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_925_, lean_object* v_m_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4(v_00_u03b2_925_, v_m_926_);
lean_dec_ref(v_m_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_928_, lean_object* v_m_929_, lean_object* v_query_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___redArg(v_m_929_, v_query_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_932_, lean_object* v_m_933_, lean_object* v_query_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_00_u03b2_932_, v_m_933_, v_query_934_);
lean_dec_ref(v_m_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_936_, lean_object* v_m_937_, lean_object* v_query_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_m_937_, v_query_938_, v_x_939_, v_x_940_, v_x_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_944_, lean_object* v_m_945_, lean_object* v_query_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_944_, v_m_945_, v_query_946_, v_x_947_, v_x_948_, v_x_949_, v_x_950_);
lean_dec_ref(v_m_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12(lean_object* v_00_u03b2_952_, lean_object* v_init_953_, lean_object* v_b_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___redArg(v_init_953_, v_b_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12___boxed(lean_object* v_00_u03b2_956_, lean_object* v_init_957_, lean_object* v_b_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12(v_00_u03b2_956_, v_init_957_, v_b_958_);
lean_dec_ref(v_b_958_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13(lean_object* v_00_u03b2_960_, lean_object* v_b_961_, lean_object* v_acc_962_, lean_object* v_i_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___redArg(v_b_961_, v_acc_962_, v_i_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13___boxed(lean_object* v_00_u03b2_965_, lean_object* v_b_966_, lean_object* v_acc_967_, lean_object* v_i_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__4_spec__12_spec__13(v_00_u03b2_965_, v_b_966_, v_acc_967_, v_i_968_);
lean_dec_ref(v_b_966_);
return v_res_969_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_974_; lean_object* v___x_975_; 
v_cellCount_974_ = lean_unsigned_to_nat(16u);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v_cellCount_976_; lean_object* v___x_977_; 
v_cellCount_976_ = lean_unsigned_to_nat(16u);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_979_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_978_);
return v___x_981_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
v___x_983_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4);
return v___x_985_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v_cellCount_986_; lean_object* v___x_987_; 
v_cellCount_986_ = lean_unsigned_to_nat(16u);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v_cellCount_988_; lean_object* v___x_989_; 
v_cellCount_988_ = lean_unsigned_to_nat(16u);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_991_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
lean_ctor_set(v___x_993_, 2, v___x_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_result_998_; 
v___x_995_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_996_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__2);
v___x_997_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_995_, v_expr_994_, v___x_996_);
v_result_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_result_998_);
lean_dec_ref(v___x_997_);
return v_result_998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* v_expr_999_, lean_object* v_h__1_1000_, lean_object* v_h__2_1001_, lean_object* v_h__3_1002_, lean_object* v_h__4_1003_, lean_object* v_h__5_1004_){
_start:
{
switch(lean_obj_tag(v_expr_999_))
{
case 0:
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__5_1004_);
lean_dec(v_h__4_1003_);
lean_dec(v_h__3_1002_);
lean_dec(v_h__2_1001_);
v_a_1005_ = lean_ctor_get(v_expr_999_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v_expr_999_, 1);
v___x_1006_ = lean_apply_1(v_h__1_1000_, v_a_1005_);
return v___x_1006_;
}
case 1:
{
uint8_t v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__5_1004_);
lean_dec(v_h__4_1003_);
lean_dec(v_h__3_1002_);
lean_dec(v_h__1_1000_);
v_a_1007_ = lean_ctor_get_uint8(v_expr_999_, 0);
lean_dec_ref_known(v_expr_999_, 0);
v___x_1008_ = lean_box(v_a_1007_);
v___x_1009_ = lean_apply_1(v_h__2_1001_, v___x_1008_);
return v___x_1009_;
}
case 2:
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
lean_dec(v_h__5_1004_);
lean_dec(v_h__4_1003_);
lean_dec(v_h__2_1001_);
lean_dec(v_h__1_1000_);
v_a_1010_ = lean_ctor_get(v_expr_999_, 0);
lean_inc_ref(v_a_1010_);
lean_dec_ref_known(v_expr_999_, 1);
v___x_1011_ = lean_apply_1(v_h__3_1002_, v_a_1010_);
return v___x_1011_;
}
case 3:
{
uint8_t v_a_1012_; lean_object* v_a_1013_; lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_h__4_1003_);
lean_dec(v_h__3_1002_);
lean_dec(v_h__2_1001_);
lean_dec(v_h__1_1000_);
v_a_1012_ = lean_ctor_get_uint8(v_expr_999_, sizeof(void*)*2);
v_a_1013_ = lean_ctor_get(v_expr_999_, 0);
lean_inc_ref(v_a_1013_);
v_a_1014_ = lean_ctor_get(v_expr_999_, 1);
lean_inc_ref(v_a_1014_);
lean_dec_ref_known(v_expr_999_, 2);
v___x_1015_ = lean_box(v_a_1012_);
v___x_1016_ = lean_apply_3(v_h__5_1004_, v___x_1015_, v_a_1013_, v_a_1014_);
return v___x_1016_;
}
default: 
{
lean_object* v_a_1017_; lean_object* v_a_1018_; lean_object* v_a_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__5_1004_);
lean_dec(v_h__3_1002_);
lean_dec(v_h__2_1001_);
lean_dec(v_h__1_1000_);
v_a_1017_ = lean_ctor_get(v_expr_999_, 0);
lean_inc_ref(v_a_1017_);
v_a_1018_ = lean_ctor_get(v_expr_999_, 1);
lean_inc_ref(v_a_1018_);
v_a_1019_ = lean_ctor_get(v_expr_999_, 2);
lean_inc_ref(v_a_1019_);
lean_dec_ref_known(v_expr_999_, 3);
v___x_1020_ = lean_apply_3(v_h__4_1003_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* v_motive_1021_, lean_object* v_expr_1022_, lean_object* v_h__1_1023_, lean_object* v_h__2_1024_, lean_object* v_h__3_1025_, lean_object* v_h__4_1026_, lean_object* v_h__5_1027_){
_start:
{
switch(lean_obj_tag(v_expr_1022_))
{
case 0:
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
lean_dec(v_h__5_1027_);
lean_dec(v_h__4_1026_);
lean_dec(v_h__3_1025_);
lean_dec(v_h__2_1024_);
v_a_1028_ = lean_ctor_get(v_expr_1022_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v_expr_1022_, 1);
v___x_1029_ = lean_apply_1(v_h__1_1023_, v_a_1028_);
return v___x_1029_;
}
case 1:
{
uint8_t v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__5_1027_);
lean_dec(v_h__4_1026_);
lean_dec(v_h__3_1025_);
lean_dec(v_h__1_1023_);
v_a_1030_ = lean_ctor_get_uint8(v_expr_1022_, 0);
lean_dec_ref_known(v_expr_1022_, 0);
v___x_1031_ = lean_box(v_a_1030_);
v___x_1032_ = lean_apply_1(v_h__2_1024_, v___x_1031_);
return v___x_1032_;
}
case 2:
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__5_1027_);
lean_dec(v_h__4_1026_);
lean_dec(v_h__2_1024_);
lean_dec(v_h__1_1023_);
v_a_1033_ = lean_ctor_get(v_expr_1022_, 0);
lean_inc_ref(v_a_1033_);
lean_dec_ref_known(v_expr_1022_, 1);
v___x_1034_ = lean_apply_1(v_h__3_1025_, v_a_1033_);
return v___x_1034_;
}
case 3:
{
uint8_t v_a_1035_; lean_object* v_a_1036_; lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__4_1026_);
lean_dec(v_h__3_1025_);
lean_dec(v_h__2_1024_);
lean_dec(v_h__1_1023_);
v_a_1035_ = lean_ctor_get_uint8(v_expr_1022_, sizeof(void*)*2);
v_a_1036_ = lean_ctor_get(v_expr_1022_, 0);
lean_inc_ref(v_a_1036_);
v_a_1037_ = lean_ctor_get(v_expr_1022_, 1);
lean_inc_ref(v_a_1037_);
lean_dec_ref_known(v_expr_1022_, 2);
v___x_1038_ = lean_box(v_a_1035_);
v___x_1039_ = lean_apply_3(v_h__5_1027_, v___x_1038_, v_a_1036_, v_a_1037_);
return v___x_1039_;
}
default: 
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v___x_1043_; 
lean_dec(v_h__5_1027_);
lean_dec(v_h__3_1025_);
lean_dec(v_h__2_1024_);
lean_dec(v_h__1_1023_);
v_a_1040_ = lean_ctor_get(v_expr_1022_, 0);
lean_inc_ref(v_a_1040_);
v_a_1041_ = lean_ctor_get(v_expr_1022_, 1);
lean_inc_ref(v_a_1041_);
v_a_1042_ = lean_ctor_get(v_expr_1022_, 2);
lean_inc_ref(v_a_1042_);
lean_dec_ref_known(v_expr_1022_, 3);
v___x_1043_ = lean_apply_3(v_h__4_1026_, v_a_1040_, v_a_1041_, v_a_1042_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* v_x_1044_, lean_object* v_h__1_1045_){
_start:
{
lean_object* v_result_1046_; lean_object* v_cache_1047_; lean_object* v_aig_1048_; lean_object* v_ref_1049_; lean_object* v___x_1050_; 
v_result_1046_ = lean_ctor_get(v_x_1044_, 0);
lean_inc_ref(v_result_1046_);
v_cache_1047_ = lean_ctor_get(v_x_1044_, 1);
lean_inc_ref(v_cache_1047_);
lean_dec_ref(v_x_1044_);
v_aig_1048_ = lean_ctor_get(v_result_1046_, 0);
lean_inc_ref(v_aig_1048_);
v_ref_1049_ = lean_ctor_get(v_result_1046_, 1);
lean_inc_ref(v_ref_1049_);
lean_dec_ref(v_result_1046_);
v___x_1050_ = lean_apply_4(v_h__1_1045_, v_aig_1048_, v_ref_1049_, lean_box(0), v_cache_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* v_aig_1051_, lean_object* v_motive_1052_, lean_object* v_x_1053_, lean_object* v_h__1_1054_){
_start:
{
lean_object* v_result_1055_; lean_object* v_cache_1056_; lean_object* v_aig_1057_; lean_object* v_ref_1058_; lean_object* v___x_1059_; 
v_result_1055_ = lean_ctor_get(v_x_1053_, 0);
lean_inc_ref(v_result_1055_);
v_cache_1056_ = lean_ctor_get(v_x_1053_, 1);
lean_inc_ref(v_cache_1056_);
lean_dec_ref(v_x_1053_);
v_aig_1057_ = lean_ctor_get(v_result_1055_, 0);
lean_inc_ref(v_aig_1057_);
v_ref_1058_ = lean_ctor_get(v_result_1055_, 1);
lean_inc_ref(v_ref_1058_);
lean_dec_ref(v_result_1055_);
v___x_1059_ = lean_apply_4(v_h__1_1054_, v_aig_1057_, v_ref_1058_, lean_box(0), v_cache_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* v_aig_1060_, lean_object* v_motive_1061_, lean_object* v_x_1062_, lean_object* v_h__1_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_1060_, v_motive_1061_, v_x_1062_, v_h__1_1063_);
lean_dec_ref(v_aig_1060_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t v_g_1065_, lean_object* v_h__1_1066_, lean_object* v_h__2_1067_, lean_object* v_h__3_1068_, lean_object* v_h__4_1069_){
_start:
{
switch(v_g_1065_)
{
case 0:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__4_1069_);
lean_dec(v_h__3_1068_);
lean_dec(v_h__2_1067_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_apply_1(v_h__1_1066_, v___x_1070_);
return v___x_1071_;
}
case 1:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__4_1069_);
lean_dec(v_h__3_1068_);
lean_dec(v_h__1_1066_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_apply_1(v_h__2_1067_, v___x_1072_);
return v___x_1073_;
}
case 2:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__4_1069_);
lean_dec(v_h__2_1067_);
lean_dec(v_h__1_1066_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_apply_1(v_h__3_1068_, v___x_1074_);
return v___x_1075_;
}
default: 
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__3_1068_);
lean_dec(v_h__2_1067_);
lean_dec(v_h__1_1066_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_apply_1(v_h__4_1069_, v___x_1076_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* v_g_1078_, lean_object* v_h__1_1079_, lean_object* v_h__2_1080_, lean_object* v_h__3_1081_, lean_object* v_h__4_1082_){
_start:
{
uint8_t v_g_42__boxed_1083_; lean_object* v_res_1084_; 
v_g_42__boxed_1083_ = lean_unbox(v_g_1078_);
v_res_1084_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_42__boxed_1083_, v_h__1_1079_, v_h__2_1080_, v_h__3_1081_, v_h__4_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* v_motive_1085_, uint8_t v_g_1086_, lean_object* v_h__1_1087_, lean_object* v_h__2_1088_, lean_object* v_h__3_1089_, lean_object* v_h__4_1090_){
_start:
{
switch(v_g_1086_)
{
case 0:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__4_1090_);
lean_dec(v_h__3_1089_);
lean_dec(v_h__2_1088_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_apply_1(v_h__1_1087_, v___x_1091_);
return v___x_1092_;
}
case 1:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__4_1090_);
lean_dec(v_h__3_1089_);
lean_dec(v_h__1_1087_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_apply_1(v_h__2_1088_, v___x_1093_);
return v___x_1094_;
}
case 2:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__4_1090_);
lean_dec(v_h__2_1088_);
lean_dec(v_h__1_1087_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_apply_1(v_h__3_1089_, v___x_1095_);
return v___x_1096_;
}
default: 
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__3_1089_);
lean_dec(v_h__2_1088_);
lean_dec(v_h__1_1087_);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_apply_1(v_h__4_1090_, v___x_1097_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* v_motive_1099_, lean_object* v_g_1100_, lean_object* v_h__1_1101_, lean_object* v_h__2_1102_, lean_object* v_h__3_1103_, lean_object* v_h__4_1104_){
_start:
{
uint8_t v_g_61__boxed_1105_; lean_object* v_res_1106_; 
v_g_61__boxed_1105_ = lean_unbox(v_g_1100_);
v_res_1106_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_1099_, v_g_61__boxed_1105_, v_h__1_1101_, v_h__2_1102_, v_h__3_1103_, v_h__4_1104_);
return v_res_1106_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0 = _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
}
#ifdef __cplusplus
}
#endif
