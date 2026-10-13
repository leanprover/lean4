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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
lean_dec(v_a_1_);
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_key_4_);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_x_2_, 3);
v___x_6_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_1_);
v___x_7_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_6_, v_key_4_, v_a_1_);
if (v___x_7_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
lean_dec(v_tail_5_);
lean_dec(v_a_1_);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_9_, v_x_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_a_13_, lean_object* v_b_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_dec(v_b_14_);
lean_dec(v_a_13_);
return v_x_15_;
}
else
{
lean_object* v_key_16_; lean_object* v_value_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_31_; 
v_key_16_ = lean_ctor_get(v_x_15_, 0);
v_value_17_ = lean_ctor_get(v_x_15_, 1);
v_tail_18_ = lean_ctor_get(v_x_15_, 2);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_31_ == 0)
{
v___x_20_ = v_x_15_;
v_isShared_21_ = v_isSharedCheck_31_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_value_17_);
lean_inc(v_key_16_);
lean_dec(v_x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_31_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_13_);
lean_inc(v_key_16_);
v___x_23_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_22_, v_key_16_, v_a_13_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_13_, v_b_14_, v_tail_18_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 2, v___x_24_);
v___x_26_ = v___x_20_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_key_16_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_value_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
else
{
lean_object* v___x_29_; 
lean_dec(v_value_17_);
lean_dec(v_key_16_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v_b_14_);
lean_ctor_set(v___x_20_, 0, v_a_13_);
v___x_29_ = v___x_20_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_13_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_b_14_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v_tail_18_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_32_){
_start:
{
switch(lean_obj_tag(v_x_32_))
{
case 0:
{
uint64_t v___x_33_; 
v___x_33_ = 0ULL;
return v___x_33_;
}
case 1:
{
lean_object* v_idx_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; 
v_idx_34_ = lean_ctor_get(v_x_32_, 0);
v___x_35_ = 1ULL;
v___x_36_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_34_);
v___x_37_ = lean_uint64_mix_hash(v___x_35_, v___x_36_);
return v___x_37_;
}
default: 
{
lean_object* v_l_38_; lean_object* v_r_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; 
v_l_38_ = lean_ctor_get(v_x_32_, 0);
v_r_39_ = lean_ctor_get(v_x_32_, 1);
v___x_40_ = 2ULL;
v___x_41_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_38_);
v___x_42_ = lean_uint64_mix_hash(v___x_40_, v___x_41_);
v___x_43_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_39_);
v___x_44_ = lean_uint64_mix_hash(v___x_42_, v___x_43_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_x_45_){
_start:
{
uint64_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_x_45_);
lean_dec(v_x_45_);
v_r_47_ = lean_box_uint64(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
return v_x_48_;
}
else
{
lean_object* v_key_50_; lean_object* v_value_51_; lean_object* v_tail_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_75_; 
v_key_50_ = lean_ctor_get(v_x_49_, 0);
v_value_51_ = lean_ctor_get(v_x_49_, 1);
v_tail_52_ = lean_ctor_get(v_x_49_, 2);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_75_ == 0)
{
v___x_54_ = v_x_49_;
v_isShared_55_ = v_isSharedCheck_75_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_tail_52_);
lean_inc(v_value_51_);
lean_inc(v_key_50_);
lean_dec(v_x_49_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_75_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v_fold_60_; uint64_t v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_56_ = lean_array_get_size(v_x_48_);
v___x_57_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_key_50_);
v___x_58_ = 32ULL;
v___x_59_ = lean_uint64_shift_right(v___x_57_, v___x_58_);
v_fold_60_ = lean_uint64_xor(v___x_57_, v___x_59_);
v___x_61_ = 16ULL;
v___x_62_ = lean_uint64_shift_right(v_fold_60_, v___x_61_);
v___x_63_ = lean_uint64_xor(v_fold_60_, v___x_62_);
v___x_64_ = lean_uint64_to_usize(v___x_63_);
v___x_65_ = lean_usize_of_nat(v___x_56_);
v___x_66_ = ((size_t)1ULL);
v___x_67_ = lean_usize_sub(v___x_65_, v___x_66_);
v___x_68_ = lean_usize_land(v___x_64_, v___x_67_);
v___x_69_ = lean_array_uget_borrowed(v_x_48_, v___x_68_);
lean_inc(v___x_69_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 2, v___x_69_);
v___x_71_ = v___x_54_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_key_50_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_value_51_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___x_69_);
v___x_71_ = v_reuseFailAlloc_74_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_uset(v_x_48_, v___x_68_, v___x_71_);
v_x_48_ = v___x_72_;
v_x_49_ = v_tail_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object* v_i_76_, lean_object* v_source_77_, lean_object* v_target_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_array_get_size(v_source_77_);
v___x_80_ = lean_nat_dec_lt(v_i_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_source_77_);
lean_dec(v_i_76_);
return v_target_78_;
}
else
{
lean_object* v_es_81_; lean_object* v___x_82_; lean_object* v_source_83_; lean_object* v_target_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_es_81_ = lean_array_fget(v_source_77_, v_i_76_);
v___x_82_ = lean_box(0);
v_source_83_ = lean_array_fset(v_source_77_, v_i_76_, v___x_82_);
v_target_84_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_target_78_, v_es_81_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_76_, v___x_85_);
lean_dec(v_i_76_);
v_i_76_ = v___x_86_;
v_source_77_ = v_source_83_;
v_target_78_ = v_target_84_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_data_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_nbuckets_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_89_ = lean_array_get_size(v_data_88_);
v___x_90_ = lean_unsigned_to_nat(2u);
v_nbuckets_91_ = lean_nat_mul(v___x_89_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v_nbuckets_91_, v___x_93_);
v___x_95_ = lean_array_propagate_mark(v_data_88_, v___x_94_);
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v___x_92_, v_data_88_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_size_100_; lean_object* v_buckets_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_144_; 
v_size_100_ = lean_ctor_get(v_m_97_, 0);
v_buckets_101_ = lean_ctor_get(v_m_97_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_m_97_);
if (v_isSharedCheck_144_ == 0)
{
v___x_103_ = v_m_97_;
v_isShared_104_ = v_isSharedCheck_144_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_buckets_101_);
lean_inc(v_size_100_);
lean_dec(v_m_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_144_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v_fold_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v_bkt_118_; uint8_t v___x_119_; 
v___x_105_ = lean_array_get_size(v_buckets_101_);
v___x_106_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_a_98_);
v___x_107_ = 32ULL;
v___x_108_ = lean_uint64_shift_right(v___x_106_, v___x_107_);
v_fold_109_ = lean_uint64_xor(v___x_106_, v___x_108_);
v___x_110_ = 16ULL;
v___x_111_ = lean_uint64_shift_right(v_fold_109_, v___x_110_);
v___x_112_ = lean_uint64_xor(v_fold_109_, v___x_111_);
v___x_113_ = lean_uint64_to_usize(v___x_112_);
v___x_114_ = lean_usize_of_nat(v___x_105_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_sub(v___x_114_, v___x_115_);
v___x_117_ = lean_usize_land(v___x_113_, v___x_116_);
v_bkt_118_ = lean_array_uget_borrowed(v_buckets_101_, v___x_117_);
lean_inc(v_bkt_118_);
lean_inc(v_a_98_);
v___x_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_98_, v_bkt_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_size_x27_121_; lean_object* v___x_122_; lean_object* v_buckets_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v_size_x27_121_ = lean_nat_add(v_size_100_, v___x_120_);
lean_dec(v_size_100_);
lean_inc(v_bkt_118_);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v_a_98_);
lean_ctor_set(v___x_122_, 1, v_b_99_);
lean_ctor_set(v___x_122_, 2, v_bkt_118_);
v_buckets_x27_123_ = lean_array_uset(v_buckets_101_, v___x_117_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(4u);
v___x_125_ = lean_nat_mul(v_size_x27_121_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(3u);
v___x_127_ = lean_nat_div(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_array_get_size(v_buckets_x27_123_);
v___x_129_ = lean_nat_dec_le(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v_val_130_; lean_object* v___x_132_; 
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(v_buckets_x27_123_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_val_130_);
lean_ctor_set(v___x_103_, 0, v_size_x27_121_);
v___x_132_ = v___x_103_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_val_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_buckets_x27_123_);
lean_ctor_set(v___x_103_, 0, v_size_x27_121_);
v___x_135_ = v___x_103_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_buckets_x27_123_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v___x_137_; lean_object* v_buckets_x27_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_bkt_118_);
v___x_137_ = lean_box(0);
v_buckets_x27_138_ = lean_array_uset(v_buckets_101_, v___x_117_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_98_, v_b_99_, v_bkt_118_);
v___x_140_ = lean_array_uset(v_buckets_x27_138_, v___x_117_, v___x_139_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_140_);
v___x_142_ = v___x_103_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_size_100_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_a_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_147_; 
lean_dec(v_a_145_);
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v_tail_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_key_148_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_key_148_);
v_value_149_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_value_149_);
v_tail_150_ = lean_ctor_get(v_x_146_, 2);
lean_inc(v_tail_150_);
lean_dec_ref_known(v_x_146_, 3);
v___x_151_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_145_);
v___x_152_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_151_, v_key_148_, v_a_145_);
if (v___x_152_ == 0)
{
lean_dec(v_value_149_);
v_x_146_ = v_tail_150_;
goto _start;
}
else
{
lean_object* v___x_154_; 
lean_dec(v_tail_150_);
lean_dec(v_a_145_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_value_149_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_buckets_157_; lean_object* v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v_fold_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_buckets_157_ = lean_ctor_get(v_m_155_, 1);
v___x_158_ = lean_array_get_size(v_buckets_157_);
v___x_159_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_a_156_);
v___x_160_ = 32ULL;
v___x_161_ = lean_uint64_shift_right(v___x_159_, v___x_160_);
v_fold_162_ = lean_uint64_xor(v___x_159_, v___x_161_);
v___x_163_ = 16ULL;
v___x_164_ = lean_uint64_shift_right(v_fold_162_, v___x_163_);
v___x_165_ = lean_uint64_xor(v_fold_162_, v___x_164_);
v___x_166_ = lean_uint64_to_usize(v___x_165_);
v___x_167_ = lean_usize_of_nat(v___x_158_);
v___x_168_ = ((size_t)1ULL);
v___x_169_ = lean_usize_sub(v___x_167_, v___x_168_);
v___x_170_ = lean_usize_land(v___x_166_, v___x_169_);
v___x_171_ = lean_array_uget_borrowed(v_buckets_157_, v___x_170_);
lean_inc(v___x_171_);
v___x_172_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_156_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_m_173_, v_a_174_);
lean_dec_ref(v_m_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(lean_object* v_aig_176_, lean_object* v_ref_177_){
_start:
{
lean_object* v_gate_178_; uint8_t v_invert_179_; lean_object* v_decls_180_; lean_object* v_decl_181_; 
v_gate_178_ = lean_ctor_get(v_ref_177_, 0);
v_invert_179_ = lean_ctor_get_uint8(v_ref_177_, sizeof(void*)*1);
v_decls_180_ = lean_ctor_get(v_aig_176_, 0);
v_decl_181_ = lean_array_fget_borrowed(v_decls_180_, v_gate_178_);
if (lean_obj_tag(v_decl_181_) == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(v_invert_179_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2___boxed(lean_object* v_aig_185_, lean_object* v_ref_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v_aig_185_, v_ref_186_);
lean_dec_ref(v_ref_186_);
lean_dec_ref(v_aig_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(lean_object* v_aig_191_, lean_object* v_input_192_){
_start:
{
lean_object* v_lhs_193_; lean_object* v_rhs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_277_; 
v_lhs_193_ = lean_ctor_get(v_input_192_, 0);
v_rhs_194_ = lean_ctor_get(v_input_192_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_input_192_);
if (v_isSharedCheck_277_ == 0)
{
v___x_196_ = v_input_192_;
v_isShared_197_ = v_isSharedCheck_277_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_rhs_194_);
lean_inc(v_lhs_193_);
lean_dec(v_input_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_277_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_decls_198_; lean_object* v_cache_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_276_; 
v_decls_198_ = lean_ctor_get(v_aig_191_, 0);
v_cache_199_ = lean_ctor_get(v_aig_191_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_aig_191_);
if (v_isSharedCheck_276_ == 0)
{
v___x_201_ = v_aig_191_;
v_isShared_202_ = v_isSharedCheck_276_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_cache_199_);
lean_inc(v_decls_198_);
lean_dec(v_aig_191_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_276_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_gate_203_; uint8_t v_invert_204_; lean_object* v_gate_205_; uint8_t v_invert_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_decl_215_; 
v_gate_203_ = lean_ctor_get(v_lhs_193_, 0);
lean_inc(v_gate_203_);
v_invert_204_ = lean_ctor_get_uint8(v_lhs_193_, sizeof(void*)*1);
v_gate_205_ = lean_ctor_get(v_rhs_194_, 0);
v_invert_206_ = lean_ctor_get_uint8(v_rhs_194_, sizeof(void*)*1);
v___x_207_ = lean_unsigned_to_nat(2u);
v___x_208_ = lean_nat_mul(v_gate_203_, v___x_207_);
v___x_209_ = l_Bool_toNat(v_invert_204_);
v___x_210_ = lean_nat_lor(v___x_208_, v___x_209_);
lean_dec(v___x_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_nat_mul(v_gate_205_, v___x_207_);
v___x_212_ = l_Bool_toNat(v_invert_206_);
v___x_213_ = lean_nat_lor(v___x_211_, v___x_212_);
lean_dec(v___x_212_);
lean_dec(v___x_211_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 2);
lean_ctor_set(v___x_196_, 1, v___x_213_);
lean_ctor_set(v___x_196_, 0, v___x_210_);
v_decl_215_ = v___x_196_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_213_);
v_decl_215_ = v_reuseFailAlloc_275_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
lean_inc_ref(v_decl_215_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_cache_199_, v_decl_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_218_; 
lean_inc(v_gate_205_);
lean_inc_ref(v_cache_199_);
lean_inc_ref(v_decls_198_);
if (v_isShared_202_ == 0)
{
v___x_218_ = v___x_201_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_decls_198_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_cache_199_);
v___x_218_ = v_reuseFailAlloc_260_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
uint8_t v___y_220_; uint8_t v___y_225_; lean_object* v_lhsVal_234_; lean_object* v_rhsVal_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_258_; 
v_lhsVal_234_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_218_, v_lhs_193_);
lean_dec_ref(v_lhs_193_);
v_rhsVal_235_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_218_, v_rhs_194_);
v_isSharedCheck_258_ = !lean_is_exclusive(v_rhs_194_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_rhs_194_, 0);
lean_dec(v_unused_259_);
v___x_237_ = v_rhs_194_;
v_isShared_238_ = v_isSharedCheck_258_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_rhs_194_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_258_;
goto v_resetjp_236_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v_ref_222_; lean_object* v___x_223_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v_ref_222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_222_, 0, v___x_221_);
lean_ctor_set_uint8(v_ref_222_, sizeof(void*)*1, v___y_220_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_218_);
lean_ctor_set(v___x_223_, 1, v_ref_222_);
return v___x_223_;
}
v___jp_224_:
{
if (v___y_225_ == 0)
{
lean_dec(v_gate_203_);
v___y_220_ = v___y_225_;
goto v___jp_219_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_226_, 0, v_gate_203_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v_invert_204_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_218_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
return v___x_227_;
}
}
v___jp_228_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_229_, 0, v_gate_205_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v_invert_206_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_218_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
v___jp_231_:
{
lean_object* v_ref_232_; lean_object* v___x_233_; 
v_ref_232_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0));
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_218_);
lean_ctor_set(v___x_233_, 1, v_ref_232_);
return v___x_233_;
}
v_resetjp_236_:
{
if (lean_obj_tag(v_lhsVal_234_) == 1)
{
lean_object* v_val_239_; uint8_t v___x_240_; 
lean_del_object(v___x_237_);
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_203_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
v_val_239_ = lean_ctor_get(v_lhsVal_234_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v_lhsVal_234_, 1);
v___x_240_ = lean_unbox(v_val_239_);
lean_dec(v_val_239_);
if (v___x_240_ == 0)
{
lean_dec(v_rhsVal_235_);
lean_dec(v_gate_205_);
goto v___jp_231_;
}
else
{
if (lean_obj_tag(v_rhsVal_235_) == 1)
{
lean_object* v_val_241_; uint8_t v___x_242_; 
v_val_241_ = lean_ctor_get(v_rhsVal_235_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v_rhsVal_235_, 1);
v___x_242_ = lean_unbox(v_val_241_);
lean_dec(v_val_241_);
if (v___x_242_ == 0)
{
lean_dec(v_gate_205_);
goto v___jp_231_;
}
else
{
goto v___jp_228_;
}
}
else
{
lean_dec(v_rhsVal_235_);
goto v___jp_228_;
}
}
}
else
{
lean_dec(v_lhsVal_234_);
if (lean_obj_tag(v_rhsVal_235_) == 1)
{
lean_object* v_val_243_; uint8_t v___x_244_; 
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_205_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
v_val_243_ = lean_ctor_get(v_rhsVal_235_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v_rhsVal_235_, 1);
v___x_244_ = lean_unbox(v_val_243_);
lean_dec(v_val_243_);
if (v___x_244_ == 0)
{
lean_del_object(v___x_237_);
lean_dec(v_gate_203_);
goto v___jp_231_;
}
else
{
lean_object* v___x_246_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_gate_203_);
v___x_246_ = v___x_237_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_gate_203_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v_invert_204_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_218_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
}
else
{
uint8_t v___x_249_; 
lean_dec(v_rhsVal_235_);
v___x_249_ = lean_nat_dec_eq(v_gate_203_, v_gate_205_);
lean_dec(v_gate_205_);
if (v___x_249_ == 0)
{
lean_object* v_g_250_; lean_object* v_cache_251_; lean_object* v_decls_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec_ref(v___x_218_);
lean_dec(v_gate_203_);
v_g_250_ = lean_array_get_size(v_decls_198_);
lean_inc_ref(v_decl_215_);
v_cache_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_cache_199_, v_decl_215_, v_g_250_);
v_decls_252_ = lean_array_push(v_decls_198_, v_decl_215_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_decls_252_);
lean_ctor_set(v___x_253_, 1, v_cache_251_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_g_250_);
v___x_255_ = v___x_237_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_g_250_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_249_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
else
{
lean_del_object(v___x_237_);
lean_dec_ref(v_decl_215_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
if (v_invert_206_ == 0)
{
if (v_invert_204_ == 0)
{
v___y_225_ = v___x_249_;
goto v___jp_224_;
}
else
{
lean_dec(v_gate_203_);
v___y_220_ = v_invert_206_;
goto v___jp_219_;
}
}
else
{
v___y_225_ = v_invert_204_;
goto v___jp_224_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_203_);
lean_dec_ref(v_lhs_193_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_rhs_194_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_rhs_194_, 0);
lean_dec(v_unused_274_);
v___x_262_ = v_rhs_194_;
v_isShared_263_ = v_isSharedCheck_273_;
goto v_resetjp_261_;
}
else
{
lean_dec(v_rhs_194_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_273_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_val_264_; lean_object* v___x_266_; 
v_val_264_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_216_, 1);
if (v_isShared_202_ == 0)
{
v___x_266_ = v___x_201_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_decls_198_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_cache_199_);
v___x_266_ = v_reuseFailAlloc_272_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
uint8_t v___x_267_; lean_object* v___x_269_; 
v___x_267_ = 0;
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_val_264_);
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_val_264_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; 
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_267_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_266_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(lean_object* v_aig_278_, lean_object* v_input_279_){
_start:
{
lean_object* v_lhs_280_; lean_object* v_rhs_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_296_; 
v_lhs_280_ = lean_ctor_get(v_input_279_, 0);
v_rhs_281_ = lean_ctor_get(v_input_279_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_input_279_);
if (v_isSharedCheck_296_ == 0)
{
v___x_283_ = v_input_279_;
v_isShared_284_ = v_isSharedCheck_296_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_rhs_281_);
lean_inc(v_lhs_280_);
lean_dec(v_input_279_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_296_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_gate_285_; lean_object* v_gate_286_; uint8_t v___x_287_; 
v_gate_285_ = lean_ctor_get(v_lhs_280_, 0);
v_gate_286_ = lean_ctor_get(v_rhs_281_, 0);
v___x_287_ = lean_nat_dec_lt(v_gate_285_, v_gate_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_289_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_lhs_280_);
lean_ctor_set(v___x_283_, 0, v_rhs_281_);
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_rhs_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_lhs_280_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_278_, v___x_289_);
return v___x_290_;
}
}
else
{
lean_object* v___x_293_; 
if (v_isShared_284_ == 0)
{
v___x_293_ = v___x_283_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_lhs_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_rhs_281_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_278_, v___x_293_);
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object* v_aig_297_, lean_object* v_input_298_){
_start:
{
lean_object* v___y_300_; lean_object* v_lhs_340_; lean_object* v_rhs_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_385_; 
v_lhs_340_ = lean_ctor_get(v_input_298_, 0);
v_rhs_341_ = lean_ctor_get(v_input_298_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_input_298_);
if (v_isSharedCheck_385_ == 0)
{
v___x_343_ = v_input_298_;
v_isShared_344_ = v_isSharedCheck_385_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_rhs_341_);
lean_inc(v_lhs_340_);
lean_dec(v_input_298_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_385_;
goto v_resetjp_342_;
}
v___jp_299_:
{
lean_object* v_res_301_; lean_object* v_ref_302_; uint8_t v_invert_303_; 
v_res_301_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_297_, v___y_300_);
v_ref_302_ = lean_ctor_get(v_res_301_, 1);
lean_inc_ref(v_ref_302_);
v_invert_303_ = lean_ctor_get_uint8(v_ref_302_, sizeof(void*)*1);
if (v_invert_303_ == 0)
{
lean_object* v_aig_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_320_; 
v_aig_304_ = lean_ctor_get(v_res_301_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_res_301_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v_res_301_, 1);
lean_dec(v_unused_321_);
v___x_306_ = v_res_301_;
v_isShared_307_ = v_isSharedCheck_320_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_aig_304_);
lean_dec(v_res_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_320_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_gate_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_319_; 
v_gate_308_ = lean_ctor_get(v_ref_302_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_ref_302_);
if (v_isSharedCheck_319_ == 0)
{
v___x_310_ = v_ref_302_;
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_gate_308_);
lean_dec(v_ref_302_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; lean_object* v___x_314_; 
v___x_312_ = 1;
if (v_isShared_311_ == 0)
{
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_gate_308_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_312_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_314_);
v___x_316_ = v___x_306_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_aig_304_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_object* v_aig_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_338_; 
v_aig_322_ = lean_ctor_get(v_res_301_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_res_301_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v_res_301_, 1);
lean_dec(v_unused_339_);
v___x_324_ = v_res_301_;
v_isShared_325_ = v_isSharedCheck_338_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_aig_322_);
lean_dec(v_res_301_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_338_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_gate_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_337_; 
v_gate_326_ = lean_ctor_get(v_ref_302_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_ref_302_);
if (v_isSharedCheck_337_ == 0)
{
v___x_328_ = v_ref_302_;
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_gate_326_);
lean_dec(v_ref_302_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_332_; 
v___x_330_ = 0;
if (v_isShared_329_ == 0)
{
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_gate_326_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_330_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_332_);
v___x_334_ = v___x_324_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_aig_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
v_resetjp_342_:
{
lean_object* v_gate_345_; uint8_t v_invert_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_384_; 
v_gate_345_ = lean_ctor_get(v_lhs_340_, 0);
v_invert_346_ = lean_ctor_get_uint8(v_lhs_340_, sizeof(void*)*1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_lhs_340_);
if (v_isSharedCheck_384_ == 0)
{
v___x_348_ = v_lhs_340_;
v_isShared_349_ = v_isSharedCheck_384_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_gate_345_);
lean_dec(v_lhs_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_384_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint8_t v___x_350_; lean_object* v___y_352_; 
v___x_350_ = 1;
if (v_invert_346_ == 0)
{
lean_object* v___x_378_; 
if (v_isShared_349_ == 0)
{
v___x_378_ = v___x_348_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_gate_345_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_350_);
v___y_352_ = v___x_378_;
goto v___jp_351_;
}
}
else
{
uint8_t v___x_380_; lean_object* v___x_382_; 
v___x_380_ = 0;
if (v_isShared_349_ == 0)
{
v___x_382_ = v___x_348_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_gate_345_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*1, v___x_380_);
v___y_352_ = v___x_382_;
goto v___jp_351_;
}
}
v___jp_351_:
{
uint8_t v_invert_353_; 
v_invert_353_ = lean_ctor_get_uint8(v_rhs_341_, sizeof(void*)*1);
if (v_invert_353_ == 0)
{
lean_object* v_gate_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_364_; 
v_gate_354_ = lean_ctor_get(v_rhs_341_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_rhs_341_);
if (v_isSharedCheck_364_ == 0)
{
v___x_356_ = v_rhs_341_;
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_gate_354_);
lean_dec(v_rhs_341_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_gate_354_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_350_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_359_);
lean_ctor_set(v___x_343_, 0, v___y_352_);
v___x_361_ = v___x_343_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___y_352_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v___y_300_ = v___x_361_;
goto v___jp_299_;
}
}
}
}
else
{
lean_object* v_gate_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_376_; 
v_gate_365_ = lean_ctor_get(v_rhs_341_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_rhs_341_);
if (v_isSharedCheck_376_ == 0)
{
v___x_367_ = v_rhs_341_;
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_gate_365_);
lean_dec(v_rhs_341_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; lean_object* v___x_371_; 
v___x_369_ = 0;
if (v_isShared_368_ == 0)
{
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_gate_365_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_369_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_371_);
lean_ctor_set(v___x_343_, 0, v___y_352_);
v___x_373_ = v___x_343_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___y_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v___y_300_ = v___x_373_;
goto v___jp_299_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object* v_aig_386_, lean_object* v_input_387_){
_start:
{
lean_object* v_discr_388_; lean_object* v_lhs_389_; lean_object* v_rhs_390_; lean_object* v___x_391_; lean_object* v_res_392_; lean_object* v_aig_393_; lean_object* v_ref_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_447_; 
v_discr_388_ = lean_ctor_get(v_input_387_, 0);
lean_inc_ref_n(v_discr_388_, 2);
v_lhs_389_ = lean_ctor_get(v_input_387_, 1);
lean_inc_ref(v_lhs_389_);
v_rhs_390_ = lean_ctor_get(v_input_387_, 2);
lean_inc_ref(v_rhs_390_);
lean_dec_ref(v_input_387_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_discr_388_);
lean_ctor_set(v___x_391_, 1, v_lhs_389_);
v_res_392_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_386_, v___x_391_);
v_aig_393_ = lean_ctor_get(v_res_392_, 0);
v_ref_394_ = lean_ctor_get(v_res_392_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_res_392_);
if (v_isSharedCheck_447_ == 0)
{
v___x_396_ = v_res_392_;
v_isShared_397_ = v_isSharedCheck_447_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_ref_394_);
lean_inc(v_aig_393_);
lean_dec(v_res_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_447_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_gate_398_; uint8_t v_invert_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_446_; 
v_gate_398_ = lean_ctor_get(v_discr_388_, 0);
v_invert_399_ = lean_ctor_get_uint8(v_discr_388_, sizeof(void*)*1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_discr_388_);
if (v_isSharedCheck_446_ == 0)
{
v___x_401_ = v_discr_388_;
v_isShared_402_ = v_isSharedCheck_446_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_gate_398_);
lean_dec(v_discr_388_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_446_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_gate_403_; uint8_t v_invert_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_445_; 
v_gate_403_ = lean_ctor_get(v_rhs_390_, 0);
v_invert_404_ = lean_ctor_get_uint8(v_rhs_390_, sizeof(void*)*1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_rhs_390_);
if (v_isSharedCheck_445_ == 0)
{
v___x_406_ = v_rhs_390_;
v_isShared_407_ = v_isSharedCheck_445_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_gate_403_);
lean_dec(v_rhs_390_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_445_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_aig_409_; lean_object* v_ref_410_; 
if (v_invert_399_ == 0)
{
uint8_t v___x_437_; lean_object* v___x_439_; 
v___x_437_ = 1;
if (v_isShared_402_ == 0)
{
v___x_439_ = v___x_401_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_gate_398_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*1, v___x_437_);
v_aig_409_ = v_aig_393_;
v_ref_410_ = v___x_439_;
goto v___jp_408_;
}
}
else
{
uint8_t v___x_441_; lean_object* v___x_443_; 
v___x_441_ = 0;
if (v_isShared_402_ == 0)
{
v___x_443_ = v___x_401_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_gate_398_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*1, v___x_441_);
v_aig_409_ = v_aig_393_;
v_ref_410_ = v___x_443_;
goto v___jp_408_;
}
}
v___jp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_407_ == 0)
{
v___x_412_ = v___x_406_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_gate_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*1, v_invert_404_);
v___x_412_ = v_reuseFailAlloc_436_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_412_);
lean_ctor_set(v___x_396_, 0, v_ref_410_);
v___x_414_ = v___x_396_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_ref_410_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_435_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v_res_415_; lean_object* v_aig_416_; lean_object* v_ref_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_434_; 
v_res_415_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_409_, v___x_414_);
v_aig_416_ = lean_ctor_get(v_res_415_, 0);
v_ref_417_ = lean_ctor_get(v_res_415_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_res_415_);
if (v_isSharedCheck_434_ == 0)
{
v___x_419_ = v_res_415_;
v_isShared_420_ = v_isSharedCheck_434_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_ref_417_);
lean_inc(v_aig_416_);
lean_dec(v_res_415_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_434_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_gate_421_; uint8_t v_invert_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_433_; 
v_gate_421_ = lean_ctor_get(v_ref_394_, 0);
v_invert_422_ = lean_ctor_get_uint8(v_ref_394_, sizeof(void*)*1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_ref_394_);
if (v_isSharedCheck_433_ == 0)
{
v___x_424_ = v_ref_394_;
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_gate_421_);
lean_dec(v_ref_394_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_lhsRef_427_; 
if (v_isShared_425_ == 0)
{
v_lhsRef_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_gate_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*1, v_invert_422_);
v_lhsRef_427_ = v_reuseFailAlloc_432_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_lhsRef_427_);
v___x_429_ = v___x_419_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_lhsRef_427_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_ref_417_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_416_, v___x_429_);
return v___x_430_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(lean_object* v_aig_448_, lean_object* v_input_449_){
_start:
{
lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v_lhs_456_; lean_object* v_rhs_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_570_; 
v_lhs_456_ = lean_ctor_get(v_input_449_, 0);
v_rhs_457_ = lean_ctor_get(v_input_449_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_input_449_);
if (v_isSharedCheck_570_ == 0)
{
v___x_459_ = v_input_449_;
v_isShared_460_ = v_isSharedCheck_570_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_rhs_457_);
lean_inc(v_lhs_456_);
lean_dec(v_input_449_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_570_;
goto v_resetjp_458_;
}
v___jp_450_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___y_452_);
lean_ctor_set(v___x_454_, 1, v___y_453_);
v___x_455_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_451_, v___x_454_);
return v___x_455_;
}
v_resetjp_458_:
{
lean_object* v_gate_461_; uint8_t v_invert_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_569_; 
v_gate_461_ = lean_ctor_get(v_lhs_456_, 0);
v_invert_462_ = lean_ctor_get_uint8(v_lhs_456_, sizeof(void*)*1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_lhs_456_);
if (v_isSharedCheck_569_ == 0)
{
v___x_464_ = v_lhs_456_;
v_isShared_465_ = v_isSharedCheck_569_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_gate_461_);
lean_dec(v_lhs_456_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_569_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; uint8_t v___x_467_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_534_; lean_object* v___y_559_; 
v___x_466_ = 0;
v___x_467_ = 1;
if (v_invert_462_ == 0)
{
lean_object* v___x_567_; 
lean_inc(v_gate_461_);
v___x_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_567_, 0, v_gate_461_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*1, v___x_466_);
v___y_559_ = v___x_567_;
goto v___jp_558_;
}
else
{
lean_object* v___x_568_; 
lean_inc(v_gate_461_);
v___x_568_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_568_, 0, v_gate_461_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*1, v___x_467_);
v___y_559_ = v___x_568_;
goto v___jp_558_;
}
v___jp_468_:
{
uint8_t v_invert_472_; 
v_invert_472_ = lean_ctor_get_uint8(v___y_469_, sizeof(void*)*1);
if (v_invert_472_ == 0)
{
lean_object* v_gate_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_gate_473_ = lean_ctor_get(v___y_469_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_469_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___y_469_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_gate_473_);
lean_dec(v___y_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_gate_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*1, v___x_467_);
v___y_451_ = v___y_470_;
v___y_452_ = v___y_471_;
v___y_453_ = v___x_478_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v_gate_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_gate_481_ = lean_ctor_get(v___y_469_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___y_469_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___y_469_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_gate_481_);
lean_dec(v___y_469_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_gate_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_466_);
v___y_451_ = v___y_470_;
v___y_452_ = v___y_471_;
v___y_453_ = v___x_486_;
goto v___jp_450_;
}
}
}
}
v___jp_489_:
{
lean_object* v_res_493_; uint8_t v_invert_494_; 
v_res_493_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_491_, v___y_492_);
v_invert_494_ = lean_ctor_get_uint8(v___y_490_, sizeof(void*)*1);
if (v_invert_494_ == 0)
{
lean_object* v_aig_495_; lean_object* v_ref_496_; lean_object* v_gate_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_aig_495_ = lean_ctor_get(v_res_493_, 0);
lean_inc_ref(v_aig_495_);
v_ref_496_ = lean_ctor_get(v_res_493_, 1);
lean_inc_ref(v_ref_496_);
lean_dec_ref(v_res_493_);
v_gate_497_ = lean_ctor_get(v___y_490_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___y_490_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___y_490_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_gate_497_);
lean_dec(v___y_490_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_gate_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_467_);
v___y_469_ = v_ref_496_;
v___y_470_ = v_aig_495_;
v___y_471_ = v___x_502_;
goto v___jp_468_;
}
}
}
else
{
lean_object* v_aig_505_; lean_object* v_ref_506_; lean_object* v_gate_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_aig_505_ = lean_ctor_get(v_res_493_, 0);
lean_inc_ref(v_aig_505_);
v_ref_506_ = lean_ctor_get(v_res_493_, 1);
lean_inc_ref(v_ref_506_);
lean_dec_ref(v_res_493_);
v_gate_507_ = lean_ctor_get(v___y_490_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___y_490_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___y_490_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_gate_507_);
lean_dec(v___y_490_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_gate_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_466_);
v___y_469_ = v_ref_506_;
v___y_470_ = v_aig_505_;
v___y_471_ = v___x_512_;
goto v___jp_468_;
}
}
}
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
lean_object* v___x_522_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___y_519_);
v___x_522_ = v___x_464_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___y_519_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_466_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_522_);
lean_ctor_set(v___x_459_, 0, v___y_520_);
v___x_524_ = v___x_459_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
v___y_490_ = v___y_518_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_524_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_528_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___y_519_);
v___x_528_ = v___x_464_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___y_519_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_467_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_528_);
lean_ctor_set(v___x_459_, 0, v___y_520_);
v___x_530_ = v___x_459_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
v___y_490_ = v___y_518_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_530_;
goto v___jp_489_;
}
}
}
}
v___jp_533_:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_448_, v___y_534_);
if (v_invert_462_ == 0)
{
lean_object* v_aig_536_; lean_object* v_ref_537_; lean_object* v_gate_538_; uint8_t v_invert_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_aig_536_ = lean_ctor_get(v_res_535_, 0);
lean_inc_ref(v_aig_536_);
v_ref_537_ = lean_ctor_get(v_res_535_, 1);
lean_inc_ref(v_ref_537_);
lean_dec_ref(v_res_535_);
v_gate_538_ = lean_ctor_get(v_rhs_457_, 0);
v_invert_539_ = lean_ctor_get_uint8(v_rhs_457_, sizeof(void*)*1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_rhs_457_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v_rhs_457_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_gate_538_);
lean_dec(v_rhs_457_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_gate_461_);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_gate_461_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*1, v___x_467_);
v___y_516_ = v_invert_539_;
v___y_517_ = v_aig_536_;
v___y_518_ = v_ref_537_;
v___y_519_ = v_gate_538_;
v___y_520_ = v___x_544_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v_aig_547_; lean_object* v_ref_548_; lean_object* v_gate_549_; uint8_t v_invert_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_aig_547_ = lean_ctor_get(v_res_535_, 0);
lean_inc_ref(v_aig_547_);
v_ref_548_ = lean_ctor_get(v_res_535_, 1);
lean_inc_ref(v_ref_548_);
lean_dec_ref(v_res_535_);
v_gate_549_ = lean_ctor_get(v_rhs_457_, 0);
v_invert_550_ = lean_ctor_get_uint8(v_rhs_457_, sizeof(void*)*1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_rhs_457_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v_rhs_457_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_gate_549_);
lean_dec(v_rhs_457_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_gate_461_);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_gate_461_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_466_);
v___y_516_ = v_invert_550_;
v___y_517_ = v_aig_547_;
v___y_518_ = v_ref_548_;
v___y_519_ = v_gate_549_;
v___y_520_ = v___x_555_;
goto v___jp_515_;
}
}
}
}
v___jp_558_:
{
uint8_t v_invert_560_; 
v_invert_560_ = lean_ctor_get_uint8(v_rhs_457_, sizeof(void*)*1);
if (v_invert_560_ == 0)
{
lean_object* v_gate_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_gate_561_ = lean_ctor_get(v_rhs_457_, 0);
lean_inc(v_gate_561_);
v___x_562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_562_, 0, v_gate_561_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_467_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_559_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___y_534_ = v___x_563_;
goto v___jp_533_;
}
else
{
lean_object* v_gate_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_gate_564_ = lean_ctor_get(v_rhs_457_, 0);
lean_inc(v_gate_564_);
v___x_565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_565_, 0, v_gate_564_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_466_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___y_559_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___y_534_ = v___x_566_;
goto v___jp_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(lean_object* v_aig_571_, lean_object* v_input_572_){
_start:
{
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v_res_602_; lean_object* v_aig_603_; lean_object* v_ref_604_; lean_object* v___y_606_; lean_object* v_lhs_631_; lean_object* v_rhs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_671_; 
lean_inc_ref(v_input_572_);
v_res_602_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_571_, v_input_572_);
v_aig_603_ = lean_ctor_get(v_res_602_, 0);
lean_inc_ref(v_aig_603_);
v_ref_604_ = lean_ctor_get(v_res_602_, 1);
lean_inc_ref(v_ref_604_);
lean_dec_ref(v_res_602_);
v_lhs_631_ = lean_ctor_get(v_input_572_, 0);
v_rhs_632_ = lean_ctor_get(v_input_572_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_input_572_);
if (v_isSharedCheck_671_ == 0)
{
v___x_634_ = v_input_572_;
v_isShared_635_ = v_isSharedCheck_671_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_rhs_632_);
lean_inc(v_lhs_631_);
lean_dec(v_input_572_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_671_;
goto v_resetjp_633_;
}
v___jp_573_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___y_575_);
lean_ctor_set(v___x_577_, 1, v___y_576_);
v___x_578_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_574_, v___x_577_);
return v___x_578_;
}
v___jp_579_:
{
uint8_t v_invert_583_; 
v_invert_583_ = lean_ctor_get_uint8(v___y_580_, sizeof(void*)*1);
if (v_invert_583_ == 0)
{
lean_object* v_gate_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_gate_584_ = lean_ctor_get(v___y_580_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___y_580_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___y_580_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_gate_584_);
lean_dec(v___y_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v___x_588_; lean_object* v___x_590_; 
v___x_588_ = 1;
if (v_isShared_587_ == 0)
{
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_gate_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*1, v___x_588_);
v___y_574_ = v___y_581_;
v___y_575_ = v___y_582_;
v___y_576_ = v___x_590_;
goto v___jp_573_;
}
}
}
else
{
lean_object* v_gate_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_gate_593_ = lean_ctor_get(v___y_580_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___y_580_);
if (v_isSharedCheck_601_ == 0)
{
v___x_595_ = v___y_580_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_gate_593_);
lean_dec(v___y_580_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; lean_object* v___x_599_; 
v___x_597_ = 0;
if (v_isShared_596_ == 0)
{
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_gate_593_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_597_);
v___y_574_ = v___y_581_;
v___y_575_ = v___y_582_;
v___y_576_ = v___x_599_;
goto v___jp_573_;
}
}
}
}
v___jp_605_:
{
lean_object* v_res_607_; uint8_t v_invert_608_; 
v_res_607_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_603_, v___y_606_);
v_invert_608_ = lean_ctor_get_uint8(v_ref_604_, sizeof(void*)*1);
if (v_invert_608_ == 0)
{
lean_object* v_aig_609_; lean_object* v_ref_610_; lean_object* v_gate_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_aig_609_ = lean_ctor_get(v_res_607_, 0);
lean_inc_ref(v_aig_609_);
v_ref_610_ = lean_ctor_get(v_res_607_, 1);
lean_inc_ref(v_ref_610_);
lean_dec_ref(v_res_607_);
v_gate_611_ = lean_ctor_get(v_ref_604_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_ref_604_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v_ref_604_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_gate_611_);
lean_dec(v_ref_604_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; lean_object* v___x_617_; 
v___x_615_ = 1;
if (v_isShared_614_ == 0)
{
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_gate_611_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*1, v___x_615_);
v___y_580_ = v_ref_610_;
v___y_581_ = v_aig_609_;
v___y_582_ = v___x_617_;
goto v___jp_579_;
}
}
}
else
{
lean_object* v_aig_620_; lean_object* v_ref_621_; lean_object* v_gate_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
v_aig_620_ = lean_ctor_get(v_res_607_, 0);
lean_inc_ref(v_aig_620_);
v_ref_621_ = lean_ctor_get(v_res_607_, 1);
lean_inc_ref(v_ref_621_);
lean_dec_ref(v_res_607_);
v_gate_622_ = lean_ctor_get(v_ref_604_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_ref_604_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v_ref_604_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_gate_622_);
lean_dec(v_ref_604_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; lean_object* v___x_628_; 
v___x_626_ = 0;
if (v_isShared_625_ == 0)
{
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_gate_622_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_626_);
v___y_580_ = v_ref_621_;
v___y_581_ = v_aig_620_;
v___y_582_ = v___x_628_;
goto v___jp_579_;
}
}
}
}
v_resetjp_633_:
{
lean_object* v_gate_636_; uint8_t v_invert_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_670_; 
v_gate_636_ = lean_ctor_get(v_lhs_631_, 0);
v_invert_637_ = lean_ctor_get_uint8(v_lhs_631_, sizeof(void*)*1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_lhs_631_);
if (v_isSharedCheck_670_ == 0)
{
v___x_639_ = v_lhs_631_;
v_isShared_640_ = v_isSharedCheck_670_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_gate_636_);
lean_dec(v_lhs_631_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_670_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_gate_641_; uint8_t v_invert_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_669_; 
v_gate_641_ = lean_ctor_get(v_rhs_632_, 0);
v_invert_642_ = lean_ctor_get_uint8(v_rhs_632_, sizeof(void*)*1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_rhs_632_);
if (v_isSharedCheck_669_ == 0)
{
v___x_644_ = v_rhs_632_;
v_isShared_645_ = v_isSharedCheck_669_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_gate_641_);
lean_dec(v_rhs_632_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_669_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; lean_object* v___y_648_; 
v___x_646_ = 1;
if (v_invert_637_ == 0)
{
lean_object* v___x_663_; 
if (v_isShared_640_ == 0)
{
v___x_663_ = v___x_639_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_gate_636_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*1, v___x_646_);
v___y_648_ = v___x_663_;
goto v___jp_647_;
}
}
else
{
uint8_t v___x_665_; lean_object* v___x_667_; 
v___x_665_ = 0;
if (v_isShared_640_ == 0)
{
v___x_667_ = v___x_639_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_gate_636_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*1, v___x_665_);
v___y_648_ = v___x_667_;
goto v___jp_647_;
}
}
v___jp_647_:
{
if (v_invert_642_ == 0)
{
lean_object* v___x_650_; 
if (v_isShared_645_ == 0)
{
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_gate_641_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_646_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_650_);
lean_ctor_set(v___x_634_, 0, v___y_648_);
v___x_652_ = v___x_634_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___y_648_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v___y_606_ = v___x_652_;
goto v___jp_605_;
}
}
}
else
{
uint8_t v___x_655_; lean_object* v___x_657_; 
v___x_655_ = 0;
if (v_isShared_645_ == 0)
{
v___x_657_ = v___x_644_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_gate_641_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_659_; 
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*1, v___x_655_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_657_);
lean_ctor_set(v___x_634_, 0, v___y_648_);
v___x_659_ = v___x_634_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___y_648_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v___y_606_ = v___x_659_;
goto v___jp_605_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object* v_aig_672_, lean_object* v_expr_673_, lean_object* v_cache_674_){
_start:
{
switch(lean_obj_tag(v_expr_673_))
{
case 0:
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_675_ = lean_ctor_get(v_expr_673_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v_expr_673_, 1);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_a_675_);
lean_ctor_set(v___x_676_, 1, v_cache_674_);
v___x_677_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_672_, v___x_676_);
return v___x_677_;
}
case 1:
{
uint8_t v_a_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_a_678_ = lean_ctor_get_uint8(v_expr_673_, 0);
lean_dec_ref_known(v_expr_673_, 0);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v_a_678_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_aig_672_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_cache_674_);
return v___x_682_;
}
case 2:
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v_result_685_; lean_object* v_ref_686_; uint8_t v_invert_687_; 
v_a_683_ = lean_ctor_get(v_expr_673_, 0);
lean_inc_ref(v_a_683_);
lean_dec_ref_known(v_expr_673_, 1);
v___x_684_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_672_, v_a_683_, v_cache_674_);
v_result_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_result_685_);
v_ref_686_ = lean_ctor_get(v_result_685_, 1);
lean_inc_ref(v_ref_686_);
v_invert_687_ = lean_ctor_get_uint8(v_ref_686_, sizeof(void*)*1);
if (v_invert_687_ == 0)
{
lean_object* v_cache_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_713_; 
v_cache_688_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_714_);
v___x_690_ = v___x_684_;
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_cache_688_);
lean_dec(v___x_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_aig_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_711_; 
v_aig_692_ = lean_ctor_get(v_result_685_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_result_685_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_result_685_, 1);
lean_dec(v_unused_712_);
v___x_694_ = v_result_685_;
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_aig_692_);
lean_dec(v_result_685_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_gate_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_710_; 
v_gate_696_ = lean_ctor_get(v_ref_686_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_ref_686_);
if (v_isSharedCheck_710_ == 0)
{
v___x_698_ = v_ref_686_;
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_gate_696_);
lean_dec(v_ref_686_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint8_t v___x_700_; lean_object* v___x_702_; 
v___x_700_ = 1;
if (v_isShared_699_ == 0)
{
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_gate_696_);
v___x_702_ = v_reuseFailAlloc_709_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_700_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_702_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_aig_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_704_);
v___x_706_ = v___x_690_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_cache_688_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
}
else
{
lean_object* v_cache_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_740_; 
v_cache_715_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_741_);
v___x_717_ = v___x_684_;
v_isShared_718_ = v_isSharedCheck_740_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_cache_715_);
lean_dec(v___x_684_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_740_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_aig_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_738_; 
v_aig_719_ = lean_ctor_get(v_result_685_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v_result_685_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_result_685_, 1);
lean_dec(v_unused_739_);
v___x_721_ = v_result_685_;
v_isShared_722_ = v_isSharedCheck_738_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_aig_719_);
lean_dec(v_result_685_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_738_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_gate_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_737_; 
v_gate_723_ = lean_ctor_get(v_ref_686_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_ref_686_);
if (v_isSharedCheck_737_ == 0)
{
v___x_725_ = v_ref_686_;
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_gate_723_);
lean_dec(v_ref_686_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
uint8_t v___x_727_; lean_object* v___x_729_; 
v___x_727_ = 0;
if (v_isShared_726_ == 0)
{
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_gate_723_);
v___x_729_ = v_reuseFailAlloc_736_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_727_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_729_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_aig_719_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_731_);
v___x_733_ = v___x_717_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_cache_715_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
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
uint8_t v_a_742_; lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v_result_746_; lean_object* v_cache_747_; lean_object* v_aig_748_; lean_object* v_ref_749_; lean_object* v___x_750_; lean_object* v_result_751_; lean_object* v_cache_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_790_; 
v_a_742_ = lean_ctor_get_uint8(v_expr_673_, sizeof(void*)*2);
v_a_743_ = lean_ctor_get(v_expr_673_, 0);
lean_inc_ref(v_a_743_);
v_a_744_ = lean_ctor_get(v_expr_673_, 1);
lean_inc_ref(v_a_744_);
lean_dec_ref_known(v_expr_673_, 2);
v___x_745_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_672_, v_a_743_, v_cache_674_);
v_result_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_result_746_);
v_cache_747_ = lean_ctor_get(v___x_745_, 1);
lean_inc_ref(v_cache_747_);
lean_dec_ref(v___x_745_);
v_aig_748_ = lean_ctor_get(v_result_746_, 0);
lean_inc_ref(v_aig_748_);
v_ref_749_ = lean_ctor_get(v_result_746_, 1);
lean_inc_ref(v_ref_749_);
lean_dec_ref(v_result_746_);
v___x_750_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_748_, v_a_744_, v_cache_747_);
v_result_751_ = lean_ctor_get(v___x_750_, 0);
v_cache_752_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_790_ == 0)
{
v___x_754_ = v___x_750_;
v_isShared_755_ = v_isSharedCheck_790_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_cache_752_);
lean_inc(v_result_751_);
lean_dec(v___x_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_790_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_aig_756_; lean_object* v_ref_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_789_; 
v_aig_756_ = lean_ctor_get(v_result_751_, 0);
v_ref_757_ = lean_ctor_get(v_result_751_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_result_751_);
if (v_isSharedCheck_789_ == 0)
{
v___x_759_ = v_result_751_;
v_isShared_760_ = v_isSharedCheck_789_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_ref_757_);
lean_inc(v_aig_756_);
lean_dec(v_result_751_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_789_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_gate_761_; uint8_t v_invert_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_788_; 
v_gate_761_ = lean_ctor_get(v_ref_749_, 0);
v_invert_762_ = lean_ctor_get_uint8(v_ref_749_, sizeof(void*)*1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_ref_749_);
if (v_isSharedCheck_788_ == 0)
{
v___x_764_ = v_ref_749_;
v_isShared_765_ = v_isSharedCheck_788_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_gate_761_);
lean_dec(v_ref_749_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_788_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_lhsRef_767_; 
if (v_isShared_765_ == 0)
{
v_lhsRef_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_gate_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*1, v_invert_762_);
v_lhsRef_767_ = v_reuseFailAlloc_787_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v_input_769_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_lhsRef_767_);
v_input_769_ = v___x_759_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_lhsRef_767_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_ref_757_);
v_input_769_ = v_reuseFailAlloc_786_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
switch(v_a_742_)
{
case 0:
{
lean_object* v_ret_770_; lean_object* v___x_772_; 
v_ret_770_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_756_, v_input_769_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_ret_770_);
v___x_772_ = v___x_754_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_ret_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_cache_752_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
case 1:
{
lean_object* v_ret_774_; lean_object* v___x_776_; 
v_ret_774_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(v_aig_756_, v_input_769_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_ret_774_);
v___x_776_ = v___x_754_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_ret_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_cache_752_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
case 2:
{
lean_object* v_ret_778_; lean_object* v___x_780_; 
v_ret_778_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(v_aig_756_, v_input_769_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_ret_778_);
v___x_780_ = v___x_754_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_ret_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_cache_752_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
default: 
{
lean_object* v_ret_782_; lean_object* v___x_784_; 
v_ret_782_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_756_, v_input_769_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_ret_782_);
v___x_784_ = v___x_754_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_ret_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_cache_752_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
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
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_841_; 
v_a_791_ = lean_ctor_get(v_expr_673_, 0);
v_a_792_ = lean_ctor_get(v_expr_673_, 1);
v_a_793_ = lean_ctor_get(v_expr_673_, 2);
v_isSharedCheck_841_ = !lean_is_exclusive(v_expr_673_);
if (v_isSharedCheck_841_ == 0)
{
v___x_795_ = v_expr_673_;
v_isShared_796_ = v_isSharedCheck_841_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_dec(v_expr_673_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_841_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_result_798_; lean_object* v_cache_799_; lean_object* v_aig_800_; lean_object* v_ref_801_; lean_object* v___x_802_; lean_object* v_result_803_; lean_object* v_cache_804_; lean_object* v_aig_805_; lean_object* v_ref_806_; lean_object* v___x_807_; lean_object* v_result_808_; lean_object* v_cache_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_840_; 
v___x_797_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_672_, v_a_791_, v_cache_674_);
v_result_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_result_798_);
v_cache_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc_ref(v_cache_799_);
lean_dec_ref(v___x_797_);
v_aig_800_ = lean_ctor_get(v_result_798_, 0);
lean_inc_ref(v_aig_800_);
v_ref_801_ = lean_ctor_get(v_result_798_, 1);
lean_inc_ref(v_ref_801_);
lean_dec_ref(v_result_798_);
v___x_802_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_800_, v_a_792_, v_cache_799_);
v_result_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_result_803_);
v_cache_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc_ref(v_cache_804_);
lean_dec_ref(v___x_802_);
v_aig_805_ = lean_ctor_get(v_result_803_, 0);
lean_inc_ref(v_aig_805_);
v_ref_806_ = lean_ctor_get(v_result_803_, 1);
lean_inc_ref(v_ref_806_);
lean_dec_ref(v_result_803_);
v___x_807_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_805_, v_a_793_, v_cache_804_);
v_result_808_ = lean_ctor_get(v___x_807_, 0);
v_cache_809_ = lean_ctor_get(v___x_807_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_840_ == 0)
{
v___x_811_ = v___x_807_;
v_isShared_812_ = v_isSharedCheck_840_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_cache_809_);
lean_inc(v_result_808_);
lean_dec(v___x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_840_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_aig_813_; lean_object* v_ref_814_; lean_object* v_gate_815_; uint8_t v_invert_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_839_; 
v_aig_813_ = lean_ctor_get(v_result_808_, 0);
lean_inc_ref(v_aig_813_);
v_ref_814_ = lean_ctor_get(v_result_808_, 1);
lean_inc_ref(v_ref_814_);
lean_dec_ref(v_result_808_);
v_gate_815_ = lean_ctor_get(v_ref_801_, 0);
v_invert_816_ = lean_ctor_get_uint8(v_ref_801_, sizeof(void*)*1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_ref_801_);
if (v_isSharedCheck_839_ == 0)
{
v___x_818_ = v_ref_801_;
v_isShared_819_ = v_isSharedCheck_839_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_gate_815_);
lean_dec(v_ref_801_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_839_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_gate_820_; uint8_t v_invert_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_838_; 
v_gate_820_ = lean_ctor_get(v_ref_806_, 0);
v_invert_821_ = lean_ctor_get_uint8(v_ref_806_, sizeof(void*)*1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_ref_806_);
if (v_isSharedCheck_838_ == 0)
{
v___x_823_ = v_ref_806_;
v_isShared_824_ = v_isSharedCheck_838_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_gate_820_);
lean_dec(v_ref_806_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_838_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_discrRef_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_gate_815_);
v_discrRef_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_gate_815_);
v_discrRef_826_ = v_reuseFailAlloc_837_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v_lhsRef_828_; 
lean_ctor_set_uint8(v_discrRef_826_, sizeof(void*)*1, v_invert_816_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_gate_820_);
v_lhsRef_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_gate_820_);
v_lhsRef_828_ = v_reuseFailAlloc_836_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v_input_830_; 
lean_ctor_set_uint8(v_lhsRef_828_, sizeof(void*)*1, v_invert_821_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 0);
lean_ctor_set(v___x_795_, 2, v_ref_814_);
lean_ctor_set(v___x_795_, 1, v_lhsRef_828_);
lean_ctor_set(v___x_795_, 0, v_discrRef_826_);
v_input_830_ = v___x_795_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_discrRef_826_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_lhsRef_828_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ref_814_);
v_input_830_ = v_reuseFailAlloc_835_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v_ret_831_; lean_object* v___x_833_; 
v_ret_831_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(v_aig_813_, v_input_830_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_ret_831_);
v___x_833_ = v___x_811_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_ret_831_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_cache_809_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_842_, lean_object* v_m_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_m_843_, v_a_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(v_00_u03b2_846_, v_m_847_, v_a_848_);
lean_dec_ref(v_m_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_850_, lean_object* v_m_851_, lean_object* v_a_852_, lean_object* v_b_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_m_851_, v_a_852_, v_b_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_855_, lean_object* v_a_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_859_, lean_object* v_a_860_, lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_863_, lean_object* v_a_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_863_, v_a_864_, v_x_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_868_, lean_object* v_data_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_871_, lean_object* v_a_872_, lean_object* v_b_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_872_, v_b_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_876_, lean_object* v_i_877_, lean_object* v_source_878_, lean_object* v_target_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_877_, v_source_878_, v_target_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object* v_expr_885_, lean_object* v_aig_886_, lean_object* v_cache_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_886_, v_expr_885_, v_cache_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v___x_894_ = lean_unsigned_to_nat(16u);
v___x_895_ = lean_mk_array(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_900_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_902_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v___x_904_ = lean_unsigned_to_nat(16u);
v___x_905_ = lean_mk_array(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_result_913_; 
v___x_910_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_911_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_912_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v___x_910_, v_expr_909_, v___x_911_);
v_result_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_result_913_);
lean_dec_ref(v___x_912_);
return v_result_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg(lean_object* v_expr_914_, lean_object* v_h__1_915_, lean_object* v_h__2_916_, lean_object* v_h__3_917_, lean_object* v_h__4_918_, lean_object* v_h__5_919_){
_start:
{
switch(lean_obj_tag(v_expr_914_))
{
case 0:
{
lean_object* v_a_920_; lean_object* v___x_921_; 
lean_dec(v_h__5_919_);
lean_dec(v_h__4_918_);
lean_dec(v_h__3_917_);
lean_dec(v_h__2_916_);
v_a_920_ = lean_ctor_get(v_expr_914_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v_expr_914_, 1);
v___x_921_ = lean_apply_1(v_h__1_915_, v_a_920_);
return v___x_921_;
}
case 1:
{
uint8_t v_a_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_h__5_919_);
lean_dec(v_h__4_918_);
lean_dec(v_h__3_917_);
lean_dec(v_h__1_915_);
v_a_922_ = lean_ctor_get_uint8(v_expr_914_, 0);
lean_dec_ref_known(v_expr_914_, 0);
v___x_923_ = lean_box(v_a_922_);
v___x_924_ = lean_apply_1(v_h__2_916_, v___x_923_);
return v___x_924_;
}
case 2:
{
lean_object* v_a_925_; lean_object* v___x_926_; 
lean_dec(v_h__5_919_);
lean_dec(v_h__4_918_);
lean_dec(v_h__2_916_);
lean_dec(v_h__1_915_);
v_a_925_ = lean_ctor_get(v_expr_914_, 0);
lean_inc_ref(v_a_925_);
lean_dec_ref_known(v_expr_914_, 1);
v___x_926_ = lean_apply_1(v_h__3_917_, v_a_925_);
return v___x_926_;
}
case 3:
{
uint8_t v_a_927_; lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_h__4_918_);
lean_dec(v_h__3_917_);
lean_dec(v_h__2_916_);
lean_dec(v_h__1_915_);
v_a_927_ = lean_ctor_get_uint8(v_expr_914_, sizeof(void*)*2);
v_a_928_ = lean_ctor_get(v_expr_914_, 0);
lean_inc_ref(v_a_928_);
v_a_929_ = lean_ctor_get(v_expr_914_, 1);
lean_inc_ref(v_a_929_);
lean_dec_ref_known(v_expr_914_, 2);
v___x_930_ = lean_box(v_a_927_);
v___x_931_ = lean_apply_3(v_h__5_919_, v___x_930_, v_a_928_, v_a_929_);
return v___x_931_;
}
default: 
{
lean_object* v_a_932_; lean_object* v_a_933_; lean_object* v_a_934_; lean_object* v___x_935_; 
lean_dec(v_h__5_919_);
lean_dec(v_h__3_917_);
lean_dec(v_h__2_916_);
lean_dec(v_h__1_915_);
v_a_932_ = lean_ctor_get(v_expr_914_, 0);
lean_inc_ref(v_a_932_);
v_a_933_ = lean_ctor_get(v_expr_914_, 1);
lean_inc_ref(v_a_933_);
v_a_934_ = lean_ctor_get(v_expr_914_, 2);
lean_inc_ref(v_a_934_);
lean_dec_ref_known(v_expr_914_, 3);
v___x_935_ = lean_apply_3(v_h__4_918_, v_a_932_, v_a_933_, v_a_934_);
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter(lean_object* v_motive_936_, lean_object* v_expr_937_, lean_object* v_h__1_938_, lean_object* v_h__2_939_, lean_object* v_h__3_940_, lean_object* v_h__4_941_, lean_object* v_h__5_942_){
_start:
{
switch(lean_obj_tag(v_expr_937_))
{
case 0:
{
lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__5_942_);
lean_dec(v_h__4_941_);
lean_dec(v_h__3_940_);
lean_dec(v_h__2_939_);
v_a_943_ = lean_ctor_get(v_expr_937_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v_expr_937_, 1);
v___x_944_ = lean_apply_1(v_h__1_938_, v_a_943_);
return v___x_944_;
}
case 1:
{
uint8_t v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_h__5_942_);
lean_dec(v_h__4_941_);
lean_dec(v_h__3_940_);
lean_dec(v_h__1_938_);
v_a_945_ = lean_ctor_get_uint8(v_expr_937_, 0);
lean_dec_ref_known(v_expr_937_, 0);
v___x_946_ = lean_box(v_a_945_);
v___x_947_ = lean_apply_1(v_h__2_939_, v___x_946_);
return v___x_947_;
}
case 2:
{
lean_object* v_a_948_; lean_object* v___x_949_; 
lean_dec(v_h__5_942_);
lean_dec(v_h__4_941_);
lean_dec(v_h__2_939_);
lean_dec(v_h__1_938_);
v_a_948_ = lean_ctor_get(v_expr_937_, 0);
lean_inc_ref(v_a_948_);
lean_dec_ref_known(v_expr_937_, 1);
v___x_949_ = lean_apply_1(v_h__3_940_, v_a_948_);
return v___x_949_;
}
case 3:
{
uint8_t v_a_950_; lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_h__4_941_);
lean_dec(v_h__3_940_);
lean_dec(v_h__2_939_);
lean_dec(v_h__1_938_);
v_a_950_ = lean_ctor_get_uint8(v_expr_937_, sizeof(void*)*2);
v_a_951_ = lean_ctor_get(v_expr_937_, 0);
lean_inc_ref(v_a_951_);
v_a_952_ = lean_ctor_get(v_expr_937_, 1);
lean_inc_ref(v_a_952_);
lean_dec_ref_known(v_expr_937_, 2);
v___x_953_ = lean_box(v_a_950_);
v___x_954_ = lean_apply_3(v_h__5_942_, v___x_953_, v_a_951_, v_a_952_);
return v___x_954_;
}
default: 
{
lean_object* v_a_955_; lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v___x_958_; 
lean_dec(v_h__5_942_);
lean_dec(v_h__3_940_);
lean_dec(v_h__2_939_);
lean_dec(v_h__1_938_);
v_a_955_ = lean_ctor_get(v_expr_937_, 0);
lean_inc_ref(v_a_955_);
v_a_956_ = lean_ctor_get(v_expr_937_, 1);
lean_inc_ref(v_a_956_);
v_a_957_ = lean_ctor_get(v_expr_937_, 2);
lean_inc_ref(v_a_957_);
lean_dec_ref_known(v_expr_937_, 3);
v___x_958_ = lean_apply_3(v_h__4_941_, v_a_955_, v_a_956_, v_a_957_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___redArg(lean_object* v_x_959_, lean_object* v_h__1_960_){
_start:
{
lean_object* v_result_961_; lean_object* v_cache_962_; lean_object* v_aig_963_; lean_object* v_ref_964_; lean_object* v___x_965_; 
v_result_961_ = lean_ctor_get(v_x_959_, 0);
lean_inc_ref(v_result_961_);
v_cache_962_ = lean_ctor_get(v_x_959_, 1);
lean_inc_ref(v_cache_962_);
lean_dec_ref(v_x_959_);
v_aig_963_ = lean_ctor_get(v_result_961_, 0);
lean_inc_ref(v_aig_963_);
v_ref_964_ = lean_ctor_get(v_result_961_, 1);
lean_inc_ref(v_ref_964_);
lean_dec_ref(v_result_961_);
v___x_965_ = lean_apply_4(v_h__1_960_, v_aig_963_, v_ref_964_, lean_box(0), v_cache_962_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(lean_object* v_aig_966_, lean_object* v_motive_967_, lean_object* v_x_968_, lean_object* v_h__1_969_){
_start:
{
lean_object* v_result_970_; lean_object* v_cache_971_; lean_object* v_aig_972_; lean_object* v_ref_973_; lean_object* v___x_974_; 
v_result_970_ = lean_ctor_get(v_x_968_, 0);
lean_inc_ref(v_result_970_);
v_cache_971_ = lean_ctor_get(v_x_968_, 1);
lean_inc_ref(v_cache_971_);
lean_dec_ref(v_x_968_);
v_aig_972_ = lean_ctor_get(v_result_970_, 0);
lean_inc_ref(v_aig_972_);
v_ref_973_ = lean_ctor_get(v_result_970_, 1);
lean_inc_ref(v_ref_973_);
lean_dec_ref(v_result_970_);
v___x_974_ = lean_apply_4(v_h__1_969_, v_aig_972_, v_ref_973_, lean_box(0), v_cache_971_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___boxed(lean_object* v_aig_975_, lean_object* v_motive_976_, lean_object* v_x_977_, lean_object* v_h__1_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(v_aig_975_, v_motive_976_, v_x_977_, v_h__1_978_);
lean_dec_ref(v_aig_975_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg(uint8_t v_g_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_, lean_object* v_h__3_983_, lean_object* v_h__4_984_){
_start:
{
switch(v_g_980_)
{
case 0:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_h__4_984_);
lean_dec(v_h__3_983_);
lean_dec(v_h__2_982_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_apply_1(v_h__1_981_, v___x_985_);
return v___x_986_;
}
case 1:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_h__4_984_);
lean_dec(v_h__3_983_);
lean_dec(v_h__1_981_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v_h__2_982_, v___x_987_);
return v___x_988_;
}
case 2:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_h__4_984_);
lean_dec(v_h__2_982_);
lean_dec(v_h__1_981_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_apply_1(v_h__3_983_, v___x_989_);
return v___x_990_;
}
default: 
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v_h__3_983_);
lean_dec(v_h__2_982_);
lean_dec(v_h__1_981_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_apply_1(v_h__4_984_, v___x_991_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg___boxed(lean_object* v_g_993_, lean_object* v_h__1_994_, lean_object* v_h__2_995_, lean_object* v_h__3_996_, lean_object* v_h__4_997_){
_start:
{
uint8_t v_g_42__boxed_998_; lean_object* v_res_999_; 
v_g_42__boxed_998_ = lean_unbox(v_g_993_);
v_res_999_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg(v_g_42__boxed_998_, v_h__1_994_, v_h__2_995_, v_h__3_996_, v_h__4_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(lean_object* v_motive_1000_, uint8_t v_g_1001_, lean_object* v_h__1_1002_, lean_object* v_h__2_1003_, lean_object* v_h__3_1004_, lean_object* v_h__4_1005_){
_start:
{
switch(v_g_1001_)
{
case 0:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__4_1005_);
lean_dec(v_h__3_1004_);
lean_dec(v_h__2_1003_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_apply_1(v_h__1_1002_, v___x_1006_);
return v___x_1007_;
}
case 1:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__4_1005_);
lean_dec(v_h__3_1004_);
lean_dec(v_h__1_1002_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_apply_1(v_h__2_1003_, v___x_1008_);
return v___x_1009_;
}
case 2:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v_h__4_1005_);
lean_dec(v_h__2_1003_);
lean_dec(v_h__1_1002_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_apply_1(v_h__3_1004_, v___x_1010_);
return v___x_1011_;
}
default: 
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__3_1004_);
lean_dec(v_h__2_1003_);
lean_dec(v_h__1_1002_);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_apply_1(v_h__4_1005_, v___x_1012_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___boxed(lean_object* v_motive_1014_, lean_object* v_g_1015_, lean_object* v_h__1_1016_, lean_object* v_h__2_1017_, lean_object* v_h__3_1018_, lean_object* v_h__4_1019_){
_start:
{
uint8_t v_g_61__boxed_1020_; lean_object* v_res_1021_; 
v_g_61__boxed_1020_ = lean_unbox(v_g_1015_);
v_res_1021_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(v_motive_1014_, v_g_61__boxed_1020_, v_h__1_1016_, v_h__2_1017_, v_h__3_1018_, v_h__4_1019_);
return v_res_1021_;
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
