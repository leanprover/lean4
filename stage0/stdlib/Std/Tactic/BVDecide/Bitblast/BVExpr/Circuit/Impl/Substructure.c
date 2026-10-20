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
lean_object* v_lhs_193_; lean_object* v_rhs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_276_; 
v_lhs_193_ = lean_ctor_get(v_input_192_, 0);
v_rhs_194_ = lean_ctor_get(v_input_192_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_input_192_);
if (v_isSharedCheck_276_ == 0)
{
v___x_196_ = v_input_192_;
v_isShared_197_ = v_isSharedCheck_276_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_rhs_194_);
lean_inc(v_lhs_193_);
lean_dec(v_input_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_276_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_decls_198_; lean_object* v_cache_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_275_; 
v_decls_198_ = lean_ctor_get(v_aig_191_, 0);
v_cache_199_ = lean_ctor_get(v_aig_191_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_aig_191_);
if (v_isSharedCheck_275_ == 0)
{
v___x_201_ = v_aig_191_;
v_isShared_202_ = v_isSharedCheck_275_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_cache_199_);
lean_inc(v_decls_198_);
lean_dec(v_aig_191_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_275_;
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
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_213_);
v_decl_215_ = v_reuseFailAlloc_274_;
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
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_decls_198_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_cache_199_);
v___x_218_ = v_reuseFailAlloc_259_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
uint8_t v___y_220_; lean_object* v_lhsVal_233_; lean_object* v_rhsVal_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_257_; 
v_lhsVal_233_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_218_, v_lhs_193_);
lean_dec_ref(v_lhs_193_);
v_rhsVal_234_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_218_, v_rhs_194_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_rhs_194_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_rhs_194_, 0);
lean_dec(v_unused_258_);
v___x_236_ = v_rhs_194_;
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_rhs_194_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
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
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_225_, 0, v_gate_203_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v_invert_204_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_218_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_228_, 0, v_gate_205_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v_invert_206_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_218_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
v___jp_230_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0));
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_218_);
lean_ctor_set(v___x_232_, 1, v_ref_231_);
return v___x_232_;
}
v_resetjp_235_:
{
if (lean_obj_tag(v_lhsVal_233_) == 1)
{
lean_object* v_val_238_; uint8_t v___x_239_; 
lean_del_object(v___x_236_);
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_203_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
v_val_238_ = lean_ctor_get(v_lhsVal_233_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_lhsVal_233_, 1);
v___x_239_ = lean_unbox(v_val_238_);
lean_dec(v_val_238_);
if (v___x_239_ == 0)
{
lean_dec(v_rhsVal_234_);
lean_dec(v_gate_205_);
goto v___jp_230_;
}
else
{
if (lean_obj_tag(v_rhsVal_234_) == 1)
{
lean_object* v_val_240_; uint8_t v___x_241_; 
v_val_240_ = lean_ctor_get(v_rhsVal_234_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v_rhsVal_234_, 1);
v___x_241_ = lean_unbox(v_val_240_);
lean_dec(v_val_240_);
if (v___x_241_ == 0)
{
lean_dec(v_gate_205_);
goto v___jp_230_;
}
else
{
goto v___jp_227_;
}
}
else
{
lean_dec(v_rhsVal_234_);
goto v___jp_227_;
}
}
}
else
{
lean_dec(v_lhsVal_233_);
if (lean_obj_tag(v_rhsVal_234_) == 1)
{
lean_object* v_val_242_; uint8_t v___x_243_; 
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_205_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
v_val_242_ = lean_ctor_get(v_rhsVal_234_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v_rhsVal_234_, 1);
v___x_243_ = lean_unbox(v_val_242_);
lean_dec(v_val_242_);
if (v___x_243_ == 0)
{
lean_del_object(v___x_236_);
lean_dec(v_gate_203_);
goto v___jp_230_;
}
else
{
lean_object* v___x_245_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_gate_203_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_gate_203_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v_invert_204_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_218_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
}
}
else
{
uint8_t v___x_248_; 
lean_dec(v_rhsVal_234_);
v___x_248_ = lean_nat_dec_eq(v_gate_203_, v_gate_205_);
lean_dec(v_gate_205_);
if (v___x_248_ == 0)
{
lean_object* v_g_249_; lean_object* v_cache_250_; lean_object* v_decls_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec_ref(v___x_218_);
lean_dec(v_gate_203_);
v_g_249_ = lean_array_get_size(v_decls_198_);
lean_inc_ref(v_decl_215_);
v_cache_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_cache_199_, v_decl_215_, v_g_249_);
v_decls_251_ = lean_array_push(v_decls_198_, v_decl_215_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_decls_251_);
lean_ctor_set(v___x_252_, 1, v_cache_250_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_g_249_);
v___x_254_ = v___x_236_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_g_249_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*1, v___x_248_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_252_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
return v___x_255_;
}
}
else
{
lean_del_object(v___x_236_);
lean_dec_ref(v_decl_215_);
lean_dec_ref(v_cache_199_);
lean_dec_ref(v_decls_198_);
if (v_invert_206_ == 0)
{
if (v_invert_204_ == 0)
{
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
if (v_invert_204_ == 0)
{
lean_dec(v_gate_203_);
v___y_220_ = v_invert_204_;
goto v___jp_219_;
}
else
{
goto v___jp_224_;
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
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_decl_215_);
lean_dec(v_gate_203_);
lean_dec_ref(v_lhs_193_);
v_isSharedCheck_272_ = !lean_is_exclusive(v_rhs_194_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_rhs_194_, 0);
lean_dec(v_unused_273_);
v___x_261_ = v_rhs_194_;
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_rhs_194_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_val_263_; lean_object* v___x_265_; 
v_val_263_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v___x_216_, 1);
if (v_isShared_202_ == 0)
{
v___x_265_ = v___x_201_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_decls_198_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_cache_199_);
v___x_265_ = v_reuseFailAlloc_271_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
uint8_t v___x_266_; lean_object* v___x_268_; 
v___x_266_ = 0;
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_val_263_);
v___x_268_ = v___x_261_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_val_263_);
v___x_268_ = v_reuseFailAlloc_270_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; 
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_266_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
return v___x_269_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(lean_object* v_aig_277_, lean_object* v_input_278_){
_start:
{
lean_object* v_lhs_279_; lean_object* v_rhs_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_295_; 
v_lhs_279_ = lean_ctor_get(v_input_278_, 0);
v_rhs_280_ = lean_ctor_get(v_input_278_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_input_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_282_ = v_input_278_;
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_rhs_280_);
lean_inc(v_lhs_279_);
lean_dec(v_input_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_gate_284_; lean_object* v_gate_285_; uint8_t v___x_286_; 
v_gate_284_ = lean_ctor_get(v_lhs_279_, 0);
v_gate_285_ = lean_ctor_get(v_rhs_280_, 0);
v___x_286_ = lean_nat_dec_lt(v_gate_284_, v_gate_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_lhs_279_);
lean_ctor_set(v___x_282_, 0, v_rhs_280_);
v___x_288_ = v___x_282_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_rhs_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_lhs_279_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_277_, v___x_288_);
return v___x_289_;
}
}
else
{
lean_object* v___x_292_; 
if (v_isShared_283_ == 0)
{
v___x_292_ = v___x_282_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_lhs_279_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_rhs_280_);
v___x_292_ = v_reuseFailAlloc_294_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_277_, v___x_292_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object* v_aig_296_, lean_object* v_input_297_){
_start:
{
lean_object* v___y_299_; lean_object* v_lhs_339_; lean_object* v_rhs_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_384_; 
v_lhs_339_ = lean_ctor_get(v_input_297_, 0);
v_rhs_340_ = lean_ctor_get(v_input_297_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_input_297_);
if (v_isSharedCheck_384_ == 0)
{
v___x_342_ = v_input_297_;
v_isShared_343_ = v_isSharedCheck_384_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_rhs_340_);
lean_inc(v_lhs_339_);
lean_dec(v_input_297_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_384_;
goto v_resetjp_341_;
}
v___jp_298_:
{
lean_object* v_res_300_; lean_object* v_ref_301_; uint8_t v_invert_302_; 
v_res_300_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_296_, v___y_299_);
v_ref_301_ = lean_ctor_get(v_res_300_, 1);
lean_inc_ref(v_ref_301_);
v_invert_302_ = lean_ctor_get_uint8(v_ref_301_, sizeof(void*)*1);
if (v_invert_302_ == 0)
{
lean_object* v_aig_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_319_; 
v_aig_303_ = lean_ctor_get(v_res_300_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_res_300_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_res_300_, 1);
lean_dec(v_unused_320_);
v___x_305_ = v_res_300_;
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_aig_303_);
lean_dec(v_res_300_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_gate_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_318_; 
v_gate_307_ = lean_ctor_get(v_ref_301_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_ref_301_);
if (v_isSharedCheck_318_ == 0)
{
v___x_309_ = v_ref_301_;
v_isShared_310_ = v_isSharedCheck_318_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_gate_307_);
lean_dec(v_ref_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_318_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; lean_object* v___x_313_; 
v___x_311_ = 1;
if (v_isShared_310_ == 0)
{
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_gate_307_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_311_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_313_);
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_aig_303_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v_aig_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_337_; 
v_aig_321_ = lean_ctor_get(v_res_300_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_res_300_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_res_300_, 1);
lean_dec(v_unused_338_);
v___x_323_ = v_res_300_;
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_aig_321_);
lean_dec(v_res_300_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_gate_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_336_; 
v_gate_325_ = lean_ctor_get(v_ref_301_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_ref_301_);
if (v_isSharedCheck_336_ == 0)
{
v___x_327_ = v_ref_301_;
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_gate_325_);
lean_dec(v_ref_301_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; lean_object* v___x_331_; 
v___x_329_ = 0;
if (v_isShared_328_ == 0)
{
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_gate_325_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_329_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_331_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_aig_321_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
v_resetjp_341_:
{
lean_object* v_gate_344_; uint8_t v_invert_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_383_; 
v_gate_344_ = lean_ctor_get(v_lhs_339_, 0);
v_invert_345_ = lean_ctor_get_uint8(v_lhs_339_, sizeof(void*)*1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_lhs_339_);
if (v_isSharedCheck_383_ == 0)
{
v___x_347_ = v_lhs_339_;
v_isShared_348_ = v_isSharedCheck_383_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_gate_344_);
lean_dec(v_lhs_339_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_383_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
uint8_t v___x_349_; lean_object* v___y_351_; 
v___x_349_ = 1;
if (v_invert_345_ == 0)
{
lean_object* v___x_377_; 
if (v_isShared_348_ == 0)
{
v___x_377_ = v___x_347_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_gate_344_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_349_);
v___y_351_ = v___x_377_;
goto v___jp_350_;
}
}
else
{
uint8_t v___x_379_; lean_object* v___x_381_; 
v___x_379_ = 0;
if (v_isShared_348_ == 0)
{
v___x_381_ = v___x_347_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_gate_344_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_379_);
v___y_351_ = v___x_381_;
goto v___jp_350_;
}
}
v___jp_350_:
{
uint8_t v_invert_352_; 
v_invert_352_ = lean_ctor_get_uint8(v_rhs_340_, sizeof(void*)*1);
if (v_invert_352_ == 0)
{
lean_object* v_gate_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v_gate_353_ = lean_ctor_get(v_rhs_340_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_rhs_340_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v_rhs_340_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_gate_353_);
lean_dec(v_rhs_340_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_gate_353_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*1, v___x_349_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_358_);
lean_ctor_set(v___x_342_, 0, v___y_351_);
v___x_360_ = v___x_342_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___y_351_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v___y_299_ = v___x_360_;
goto v___jp_298_;
}
}
}
}
else
{
lean_object* v_gate_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
v_gate_364_ = lean_ctor_get(v_rhs_340_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_rhs_340_);
if (v_isSharedCheck_375_ == 0)
{
v___x_366_ = v_rhs_340_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_gate_364_);
lean_dec(v_rhs_340_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; lean_object* v___x_370_; 
v___x_368_ = 0;
if (v_isShared_367_ == 0)
{
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_gate_364_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v___x_368_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_370_);
lean_ctor_set(v___x_342_, 0, v___y_351_);
v___x_372_ = v___x_342_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___y_351_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v___y_299_ = v___x_372_;
goto v___jp_298_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object* v_aig_385_, lean_object* v_input_386_){
_start:
{
lean_object* v_discr_387_; lean_object* v_lhs_388_; lean_object* v_rhs_389_; lean_object* v___x_390_; lean_object* v_res_391_; lean_object* v_aig_392_; lean_object* v_ref_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_446_; 
v_discr_387_ = lean_ctor_get(v_input_386_, 0);
lean_inc_ref_n(v_discr_387_, 2);
v_lhs_388_ = lean_ctor_get(v_input_386_, 1);
lean_inc_ref(v_lhs_388_);
v_rhs_389_ = lean_ctor_get(v_input_386_, 2);
lean_inc_ref(v_rhs_389_);
lean_dec_ref(v_input_386_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_discr_387_);
lean_ctor_set(v___x_390_, 1, v_lhs_388_);
v_res_391_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_385_, v___x_390_);
v_aig_392_ = lean_ctor_get(v_res_391_, 0);
v_ref_393_ = lean_ctor_get(v_res_391_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_res_391_);
if (v_isSharedCheck_446_ == 0)
{
v___x_395_ = v_res_391_;
v_isShared_396_ = v_isSharedCheck_446_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_ref_393_);
lean_inc(v_aig_392_);
lean_dec(v_res_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_446_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_gate_397_; uint8_t v_invert_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_445_; 
v_gate_397_ = lean_ctor_get(v_discr_387_, 0);
v_invert_398_ = lean_ctor_get_uint8(v_discr_387_, sizeof(void*)*1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_discr_387_);
if (v_isSharedCheck_445_ == 0)
{
v___x_400_ = v_discr_387_;
v_isShared_401_ = v_isSharedCheck_445_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_gate_397_);
lean_dec(v_discr_387_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_445_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_gate_402_; uint8_t v_invert_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_444_; 
v_gate_402_ = lean_ctor_get(v_rhs_389_, 0);
v_invert_403_ = lean_ctor_get_uint8(v_rhs_389_, sizeof(void*)*1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_rhs_389_);
if (v_isSharedCheck_444_ == 0)
{
v___x_405_ = v_rhs_389_;
v_isShared_406_ = v_isSharedCheck_444_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_gate_402_);
lean_dec(v_rhs_389_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_444_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_aig_408_; lean_object* v_ref_409_; 
if (v_invert_398_ == 0)
{
uint8_t v___x_436_; lean_object* v___x_438_; 
v___x_436_ = 1;
if (v_isShared_401_ == 0)
{
v___x_438_ = v___x_400_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_gate_397_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*1, v___x_436_);
v_aig_408_ = v_aig_392_;
v_ref_409_ = v___x_438_;
goto v___jp_407_;
}
}
else
{
uint8_t v___x_440_; lean_object* v___x_442_; 
v___x_440_ = 0;
if (v_isShared_401_ == 0)
{
v___x_442_ = v___x_400_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_gate_397_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*1, v___x_440_);
v_aig_408_ = v_aig_392_;
v_ref_409_ = v___x_442_;
goto v___jp_407_;
}
}
v___jp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_406_ == 0)
{
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_gate_402_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*1, v_invert_403_);
v___x_411_ = v_reuseFailAlloc_435_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_411_);
lean_ctor_set(v___x_395_, 0, v_ref_409_);
v___x_413_ = v___x_395_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_ref_409_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_434_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v_res_414_; lean_object* v_aig_415_; lean_object* v_ref_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_433_; 
v_res_414_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_408_, v___x_413_);
v_aig_415_ = lean_ctor_get(v_res_414_, 0);
v_ref_416_ = lean_ctor_get(v_res_414_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_res_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_418_ = v_res_414_;
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_ref_416_);
lean_inc(v_aig_415_);
lean_dec(v_res_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_gate_420_; uint8_t v_invert_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
v_gate_420_ = lean_ctor_get(v_ref_393_, 0);
v_invert_421_ = lean_ctor_get_uint8(v_ref_393_, sizeof(void*)*1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_ref_393_);
if (v_isSharedCheck_432_ == 0)
{
v___x_423_ = v_ref_393_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_gate_420_);
lean_dec(v_ref_393_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_lhsRef_426_; 
if (v_isShared_424_ == 0)
{
v_lhsRef_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_gate_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*1, v_invert_421_);
v_lhsRef_426_ = v_reuseFailAlloc_431_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v_lhsRef_426_);
v___x_428_ = v___x_418_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_lhsRef_426_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_ref_416_);
v___x_428_ = v_reuseFailAlloc_430_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_415_, v___x_428_);
return v___x_429_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(lean_object* v_aig_447_, lean_object* v_input_448_){
_start:
{
lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v_lhs_455_; lean_object* v_rhs_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_569_; 
v_lhs_455_ = lean_ctor_get(v_input_448_, 0);
v_rhs_456_ = lean_ctor_get(v_input_448_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_input_448_);
if (v_isSharedCheck_569_ == 0)
{
v___x_458_ = v_input_448_;
v_isShared_459_ = v_isSharedCheck_569_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_rhs_456_);
lean_inc(v_lhs_455_);
lean_dec(v_input_448_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_569_;
goto v_resetjp_457_;
}
v___jp_449_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___y_450_);
lean_ctor_set(v___x_453_, 1, v___y_452_);
v___x_454_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_451_, v___x_453_);
return v___x_454_;
}
v_resetjp_457_:
{
lean_object* v_gate_460_; uint8_t v_invert_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_568_; 
v_gate_460_ = lean_ctor_get(v_lhs_455_, 0);
v_invert_461_ = lean_ctor_get_uint8(v_lhs_455_, sizeof(void*)*1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_lhs_455_);
if (v_isSharedCheck_568_ == 0)
{
v___x_463_ = v_lhs_455_;
v_isShared_464_ = v_isSharedCheck_568_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_gate_460_);
lean_dec(v_lhs_455_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_568_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; uint8_t v___x_466_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_533_; lean_object* v___y_558_; 
v___x_465_ = 0;
v___x_466_ = 1;
if (v_invert_461_ == 0)
{
lean_object* v___x_566_; 
lean_inc(v_gate_460_);
v___x_566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_566_, 0, v_gate_460_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_465_);
v___y_558_ = v___x_566_;
goto v___jp_557_;
}
else
{
lean_object* v___x_567_; 
lean_inc(v_gate_460_);
v___x_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_567_, 0, v_gate_460_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*1, v___x_466_);
v___y_558_ = v___x_567_;
goto v___jp_557_;
}
v___jp_467_:
{
uint8_t v_invert_471_; 
v_invert_471_ = lean_ctor_get_uint8(v___y_468_, sizeof(void*)*1);
if (v_invert_471_ == 0)
{
lean_object* v_gate_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_gate_472_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___y_468_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_gate_472_);
lean_dec(v___y_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_gate_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_466_);
v___y_450_ = v___y_470_;
v___y_451_ = v___y_469_;
v___y_452_ = v___x_477_;
goto v___jp_449_;
}
}
}
else
{
lean_object* v_gate_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_gate_480_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___y_468_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_gate_480_);
lean_dec(v___y_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_gate_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*1, v___x_465_);
v___y_450_ = v___y_470_;
v___y_451_ = v___y_469_;
v___y_452_ = v___x_485_;
goto v___jp_449_;
}
}
}
}
v___jp_488_:
{
lean_object* v_res_492_; uint8_t v_invert_493_; 
v_res_492_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_490_, v___y_491_);
v_invert_493_ = lean_ctor_get_uint8(v___y_489_, sizeof(void*)*1);
if (v_invert_493_ == 0)
{
lean_object* v_aig_494_; lean_object* v_ref_495_; lean_object* v_gate_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_aig_494_ = lean_ctor_get(v_res_492_, 0);
lean_inc_ref(v_aig_494_);
v_ref_495_ = lean_ctor_get(v_res_492_, 1);
lean_inc_ref(v_ref_495_);
lean_dec_ref(v_res_492_);
v_gate_496_ = lean_ctor_get(v___y_489_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___y_489_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___y_489_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_gate_496_);
lean_dec(v___y_489_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_gate_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_466_);
v___y_468_ = v_ref_495_;
v___y_469_ = v_aig_494_;
v___y_470_ = v___x_501_;
goto v___jp_467_;
}
}
}
else
{
lean_object* v_aig_504_; lean_object* v_ref_505_; lean_object* v_gate_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_aig_504_ = lean_ctor_get(v_res_492_, 0);
lean_inc_ref(v_aig_504_);
v_ref_505_ = lean_ctor_get(v_res_492_, 1);
lean_inc_ref(v_ref_505_);
lean_dec_ref(v_res_492_);
v_gate_506_ = lean_ctor_get(v___y_489_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___y_489_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___y_489_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_gate_506_);
lean_dec(v___y_489_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_gate_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_465_);
v___y_468_ = v_ref_505_;
v___y_469_ = v_aig_504_;
v___y_470_ = v___x_511_;
goto v___jp_467_;
}
}
}
}
v___jp_514_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_521_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___y_516_);
v___x_521_ = v___x_463_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_516_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_465_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_521_);
lean_ctor_set(v___x_458_, 0, v___y_519_);
v___x_523_ = v___x_458_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___y_519_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v___y_489_ = v___y_515_;
v___y_490_ = v___y_517_;
v___y_491_ = v___x_523_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v___x_527_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___y_516_);
v___x_527_ = v___x_463_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___y_516_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_466_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_527_);
lean_ctor_set(v___x_458_, 0, v___y_519_);
v___x_529_ = v___x_458_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___y_519_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v___y_489_ = v___y_515_;
v___y_490_ = v___y_517_;
v___y_491_ = v___x_529_;
goto v___jp_488_;
}
}
}
}
v___jp_532_:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_447_, v___y_533_);
if (v_invert_461_ == 0)
{
lean_object* v_aig_535_; lean_object* v_ref_536_; lean_object* v_gate_537_; uint8_t v_invert_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_aig_535_ = lean_ctor_get(v_res_534_, 0);
lean_inc_ref(v_aig_535_);
v_ref_536_ = lean_ctor_get(v_res_534_, 1);
lean_inc_ref(v_ref_536_);
lean_dec_ref(v_res_534_);
v_gate_537_ = lean_ctor_get(v_rhs_456_, 0);
v_invert_538_ = lean_ctor_get_uint8(v_rhs_456_, sizeof(void*)*1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_rhs_456_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v_rhs_456_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_gate_537_);
lean_dec(v_rhs_456_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_gate_460_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_gate_460_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_466_);
v___y_515_ = v_ref_536_;
v___y_516_ = v_gate_537_;
v___y_517_ = v_aig_535_;
v___y_518_ = v_invert_538_;
v___y_519_ = v___x_543_;
goto v___jp_514_;
}
}
}
else
{
lean_object* v_aig_546_; lean_object* v_ref_547_; lean_object* v_gate_548_; uint8_t v_invert_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_aig_546_ = lean_ctor_get(v_res_534_, 0);
lean_inc_ref(v_aig_546_);
v_ref_547_ = lean_ctor_get(v_res_534_, 1);
lean_inc_ref(v_ref_547_);
lean_dec_ref(v_res_534_);
v_gate_548_ = lean_ctor_get(v_rhs_456_, 0);
v_invert_549_ = lean_ctor_get_uint8(v_rhs_456_, sizeof(void*)*1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_rhs_456_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v_rhs_456_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_gate_548_);
lean_dec(v_rhs_456_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_gate_460_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_460_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_465_);
v___y_515_ = v_ref_547_;
v___y_516_ = v_gate_548_;
v___y_517_ = v_aig_546_;
v___y_518_ = v_invert_549_;
v___y_519_ = v___x_554_;
goto v___jp_514_;
}
}
}
}
v___jp_557_:
{
uint8_t v_invert_559_; 
v_invert_559_ = lean_ctor_get_uint8(v_rhs_456_, sizeof(void*)*1);
if (v_invert_559_ == 0)
{
lean_object* v_gate_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_gate_560_ = lean_ctor_get(v_rhs_456_, 0);
lean_inc(v_gate_560_);
v___x_561_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_561_, 0, v_gate_560_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_466_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___y_558_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___y_533_ = v___x_562_;
goto v___jp_532_;
}
else
{
lean_object* v_gate_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_gate_563_ = lean_ctor_get(v_rhs_456_, 0);
lean_inc(v_gate_563_);
v___x_564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_564_, 0, v_gate_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*1, v___x_465_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_558_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___y_533_ = v___x_565_;
goto v___jp_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(lean_object* v_aig_570_, lean_object* v_input_571_){
_start:
{
lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v_res_601_; lean_object* v_aig_602_; lean_object* v_ref_603_; lean_object* v___y_605_; lean_object* v_lhs_630_; lean_object* v_rhs_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_670_; 
lean_inc_ref(v_input_571_);
v_res_601_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_570_, v_input_571_);
v_aig_602_ = lean_ctor_get(v_res_601_, 0);
lean_inc_ref(v_aig_602_);
v_ref_603_ = lean_ctor_get(v_res_601_, 1);
lean_inc_ref(v_ref_603_);
lean_dec_ref(v_res_601_);
v_lhs_630_ = lean_ctor_get(v_input_571_, 0);
v_rhs_631_ = lean_ctor_get(v_input_571_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_input_571_);
if (v_isSharedCheck_670_ == 0)
{
v___x_633_ = v_input_571_;
v_isShared_634_ = v_isSharedCheck_670_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_rhs_631_);
lean_inc(v_lhs_630_);
lean_dec(v_input_571_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_670_;
goto v_resetjp_632_;
}
v___jp_572_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___y_574_);
lean_ctor_set(v___x_576_, 1, v___y_575_);
v___x_577_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_573_, v___x_576_);
return v___x_577_;
}
v___jp_578_:
{
uint8_t v_invert_582_; 
v_invert_582_ = lean_ctor_get_uint8(v___y_580_, sizeof(void*)*1);
if (v_invert_582_ == 0)
{
lean_object* v_gate_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_gate_583_ = lean_ctor_get(v___y_580_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___y_580_);
if (v_isSharedCheck_591_ == 0)
{
v___x_585_ = v___y_580_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_gate_583_);
lean_dec(v___y_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint8_t v___x_587_; lean_object* v___x_589_; 
v___x_587_ = 1;
if (v_isShared_586_ == 0)
{
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_gate_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*1, v___x_587_);
v___y_573_ = v___y_579_;
v___y_574_ = v___y_581_;
v___y_575_ = v___x_589_;
goto v___jp_572_;
}
}
}
else
{
lean_object* v_gate_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_gate_592_ = lean_ctor_get(v___y_580_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___y_580_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v___y_580_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_gate_592_);
lean_dec(v___y_580_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint8_t v___x_596_; lean_object* v___x_598_; 
v___x_596_ = 0;
if (v_isShared_595_ == 0)
{
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_gate_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*1, v___x_596_);
v___y_573_ = v___y_579_;
v___y_574_ = v___y_581_;
v___y_575_ = v___x_598_;
goto v___jp_572_;
}
}
}
}
v___jp_604_:
{
lean_object* v_res_606_; uint8_t v_invert_607_; 
v_res_606_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_602_, v___y_605_);
v_invert_607_ = lean_ctor_get_uint8(v_ref_603_, sizeof(void*)*1);
if (v_invert_607_ == 0)
{
lean_object* v_aig_608_; lean_object* v_ref_609_; lean_object* v_gate_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_618_; 
v_aig_608_ = lean_ctor_get(v_res_606_, 0);
lean_inc_ref(v_aig_608_);
v_ref_609_ = lean_ctor_get(v_res_606_, 1);
lean_inc_ref(v_ref_609_);
lean_dec_ref(v_res_606_);
v_gate_610_ = lean_ctor_get(v_ref_603_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_ref_603_);
if (v_isSharedCheck_618_ == 0)
{
v___x_612_ = v_ref_603_;
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_gate_610_);
lean_dec(v_ref_603_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; lean_object* v___x_616_; 
v___x_614_ = 1;
if (v_isShared_613_ == 0)
{
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_gate_610_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*1, v___x_614_);
v___y_579_ = v_aig_608_;
v___y_580_ = v_ref_609_;
v___y_581_ = v___x_616_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_aig_619_; lean_object* v_ref_620_; lean_object* v_gate_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v_aig_619_ = lean_ctor_get(v_res_606_, 0);
lean_inc_ref(v_aig_619_);
v_ref_620_ = lean_ctor_get(v_res_606_, 1);
lean_inc_ref(v_ref_620_);
lean_dec_ref(v_res_606_);
v_gate_621_ = lean_ctor_get(v_ref_603_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_ref_603_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v_ref_603_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_gate_621_);
lean_dec(v_ref_603_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___x_625_; lean_object* v___x_627_; 
v___x_625_ = 0;
if (v_isShared_624_ == 0)
{
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_gate_621_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_625_);
v___y_579_ = v_aig_619_;
v___y_580_ = v_ref_620_;
v___y_581_ = v___x_627_;
goto v___jp_578_;
}
}
}
}
v_resetjp_632_:
{
lean_object* v_gate_635_; uint8_t v_invert_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_669_; 
v_gate_635_ = lean_ctor_get(v_lhs_630_, 0);
v_invert_636_ = lean_ctor_get_uint8(v_lhs_630_, sizeof(void*)*1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_lhs_630_);
if (v_isSharedCheck_669_ == 0)
{
v___x_638_ = v_lhs_630_;
v_isShared_639_ = v_isSharedCheck_669_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_gate_635_);
lean_dec(v_lhs_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_669_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_gate_640_; uint8_t v_invert_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_668_; 
v_gate_640_ = lean_ctor_get(v_rhs_631_, 0);
v_invert_641_ = lean_ctor_get_uint8(v_rhs_631_, sizeof(void*)*1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_rhs_631_);
if (v_isSharedCheck_668_ == 0)
{
v___x_643_ = v_rhs_631_;
v_isShared_644_ = v_isSharedCheck_668_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_gate_640_);
lean_dec(v_rhs_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_668_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___x_645_; lean_object* v___y_647_; 
v___x_645_ = 1;
if (v_invert_636_ == 0)
{
lean_object* v___x_662_; 
if (v_isShared_639_ == 0)
{
v___x_662_ = v___x_638_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_gate_635_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*1, v___x_645_);
v___y_647_ = v___x_662_;
goto v___jp_646_;
}
}
else
{
uint8_t v___x_664_; lean_object* v___x_666_; 
v___x_664_ = 0;
if (v_isShared_639_ == 0)
{
v___x_666_ = v___x_638_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_gate_635_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*1, v___x_664_);
v___y_647_ = v___x_666_;
goto v___jp_646_;
}
}
v___jp_646_:
{
if (v_invert_641_ == 0)
{
lean_object* v___x_649_; 
if (v_isShared_644_ == 0)
{
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_gate_640_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_645_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_649_);
lean_ctor_set(v___x_633_, 0, v___y_647_);
v___x_651_ = v___x_633_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___y_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v___y_605_ = v___x_651_;
goto v___jp_604_;
}
}
}
else
{
uint8_t v___x_654_; lean_object* v___x_656_; 
v___x_654_ = 0;
if (v_isShared_644_ == 0)
{
v___x_656_ = v___x_643_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_gate_640_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_654_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_656_);
lean_ctor_set(v___x_633_, 0, v___y_647_);
v___x_658_ = v___x_633_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___y_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_605_ = v___x_658_;
goto v___jp_604_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object* v_aig_671_, lean_object* v_expr_672_, lean_object* v_cache_673_){
_start:
{
switch(lean_obj_tag(v_expr_672_))
{
case 0:
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_674_ = lean_ctor_get(v_expr_672_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v_expr_672_, 1);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_674_);
lean_ctor_set(v___x_675_, 1, v_cache_673_);
v___x_676_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_671_, v___x_675_);
return v___x_676_;
}
case 1:
{
uint8_t v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_a_677_ = lean_ctor_get_uint8(v_expr_672_, 0);
lean_dec_ref_known(v_expr_672_, 0);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v_a_677_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_aig_671_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v_cache_673_);
return v___x_681_;
}
case 2:
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v_result_684_; lean_object* v_ref_685_; uint8_t v_invert_686_; 
v_a_682_ = lean_ctor_get(v_expr_672_, 0);
lean_inc_ref(v_a_682_);
lean_dec_ref_known(v_expr_672_, 1);
v___x_683_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_671_, v_a_682_, v_cache_673_);
v_result_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref(v_result_684_);
v_ref_685_ = lean_ctor_get(v_result_684_, 1);
lean_inc_ref(v_ref_685_);
v_invert_686_ = lean_ctor_get_uint8(v_ref_685_, sizeof(void*)*1);
if (v_invert_686_ == 0)
{
lean_object* v_cache_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_712_; 
v_cache_687_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_683_, 0);
lean_dec(v_unused_713_);
v___x_689_ = v___x_683_;
v_isShared_690_ = v_isSharedCheck_712_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_cache_687_);
lean_dec(v___x_683_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_712_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_aig_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_710_; 
v_aig_691_ = lean_ctor_get(v_result_684_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_result_684_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_result_684_, 1);
lean_dec(v_unused_711_);
v___x_693_ = v_result_684_;
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_aig_691_);
lean_dec(v_result_684_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_gate_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_709_; 
v_gate_695_ = lean_ctor_get(v_ref_685_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_ref_685_);
if (v_isSharedCheck_709_ == 0)
{
v___x_697_ = v_ref_685_;
v_isShared_698_ = v_isSharedCheck_709_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_gate_695_);
lean_dec(v_ref_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_709_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
uint8_t v___x_699_; lean_object* v___x_701_; 
v___x_699_ = 1;
if (v_isShared_698_ == 0)
{
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_gate_695_);
v___x_701_ = v_reuseFailAlloc_708_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v___x_699_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_701_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_aig_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_703_);
v___x_705_ = v___x_689_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_cache_687_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
}
else
{
lean_object* v_cache_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_739_; 
v_cache_714_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v___x_683_, 0);
lean_dec(v_unused_740_);
v___x_716_ = v___x_683_;
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_cache_714_);
lean_dec(v___x_683_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_aig_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_737_; 
v_aig_718_ = lean_ctor_get(v_result_684_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_result_684_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_result_684_, 1);
lean_dec(v_unused_738_);
v___x_720_ = v_result_684_;
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_aig_718_);
lean_dec(v_result_684_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_gate_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_736_; 
v_gate_722_ = lean_ctor_get(v_ref_685_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_ref_685_);
if (v_isSharedCheck_736_ == 0)
{
v___x_724_ = v_ref_685_;
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_gate_722_);
lean_dec(v_ref_685_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint8_t v___x_726_; lean_object* v___x_728_; 
v___x_726_ = 0;
if (v_isShared_725_ == 0)
{
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_gate_722_);
v___x_728_ = v_reuseFailAlloc_735_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*1, v___x_726_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_728_);
v___x_730_ = v___x_720_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_aig_718_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_730_);
v___x_732_ = v___x_716_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_cache_714_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
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
uint8_t v_a_741_; lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v_result_745_; lean_object* v_cache_746_; lean_object* v_aig_747_; lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v_result_750_; lean_object* v_cache_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_789_; 
v_a_741_ = lean_ctor_get_uint8(v_expr_672_, sizeof(void*)*2);
v_a_742_ = lean_ctor_get(v_expr_672_, 0);
lean_inc_ref(v_a_742_);
v_a_743_ = lean_ctor_get(v_expr_672_, 1);
lean_inc_ref(v_a_743_);
lean_dec_ref_known(v_expr_672_, 2);
v___x_744_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_671_, v_a_742_, v_cache_673_);
v_result_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_result_745_);
v_cache_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc_ref(v_cache_746_);
lean_dec_ref(v___x_744_);
v_aig_747_ = lean_ctor_get(v_result_745_, 0);
lean_inc_ref(v_aig_747_);
v_ref_748_ = lean_ctor_get(v_result_745_, 1);
lean_inc_ref(v_ref_748_);
lean_dec_ref(v_result_745_);
v___x_749_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_747_, v_a_743_, v_cache_746_);
v_result_750_ = lean_ctor_get(v___x_749_, 0);
v_cache_751_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_789_ == 0)
{
v___x_753_ = v___x_749_;
v_isShared_754_ = v_isSharedCheck_789_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_cache_751_);
lean_inc(v_result_750_);
lean_dec(v___x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_789_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_aig_755_; lean_object* v_ref_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_788_; 
v_aig_755_ = lean_ctor_get(v_result_750_, 0);
v_ref_756_ = lean_ctor_get(v_result_750_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_result_750_);
if (v_isSharedCheck_788_ == 0)
{
v___x_758_ = v_result_750_;
v_isShared_759_ = v_isSharedCheck_788_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_ref_756_);
lean_inc(v_aig_755_);
lean_dec(v_result_750_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_788_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_gate_760_; uint8_t v_invert_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_787_; 
v_gate_760_ = lean_ctor_get(v_ref_748_, 0);
v_invert_761_ = lean_ctor_get_uint8(v_ref_748_, sizeof(void*)*1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_ref_748_);
if (v_isSharedCheck_787_ == 0)
{
v___x_763_ = v_ref_748_;
v_isShared_764_ = v_isSharedCheck_787_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_gate_760_);
lean_dec(v_ref_748_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_787_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_lhsRef_766_; 
if (v_isShared_764_ == 0)
{
v_lhsRef_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_gate_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_786_, sizeof(void*)*1, v_invert_761_);
v_lhsRef_766_ = v_reuseFailAlloc_786_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v_input_768_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_lhsRef_766_);
v_input_768_ = v___x_758_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_lhsRef_766_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_ref_756_);
v_input_768_ = v_reuseFailAlloc_785_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
switch(v_a_741_)
{
case 0:
{
lean_object* v_ret_769_; lean_object* v___x_771_; 
v_ret_769_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_755_, v_input_768_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_ret_769_);
v___x_771_ = v___x_753_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_ret_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_cache_751_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
case 1:
{
lean_object* v_ret_773_; lean_object* v___x_775_; 
v_ret_773_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(v_aig_755_, v_input_768_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_ret_773_);
v___x_775_ = v___x_753_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_ret_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_cache_751_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
case 2:
{
lean_object* v_ret_777_; lean_object* v___x_779_; 
v_ret_777_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(v_aig_755_, v_input_768_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_ret_777_);
v___x_779_ = v___x_753_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_ret_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_cache_751_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
default: 
{
lean_object* v_ret_781_; lean_object* v___x_783_; 
v_ret_781_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_755_, v_input_768_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_ret_781_);
v___x_783_ = v___x_753_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_ret_781_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_cache_751_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
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
lean_object* v_a_790_; lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_840_; 
v_a_790_ = lean_ctor_get(v_expr_672_, 0);
v_a_791_ = lean_ctor_get(v_expr_672_, 1);
v_a_792_ = lean_ctor_get(v_expr_672_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_expr_672_);
if (v_isSharedCheck_840_ == 0)
{
v___x_794_ = v_expr_672_;
v_isShared_795_ = v_isSharedCheck_840_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_inc(v_a_790_);
lean_dec(v_expr_672_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_840_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v_result_797_; lean_object* v_cache_798_; lean_object* v_aig_799_; lean_object* v_ref_800_; lean_object* v___x_801_; lean_object* v_result_802_; lean_object* v_cache_803_; lean_object* v_aig_804_; lean_object* v_ref_805_; lean_object* v___x_806_; lean_object* v_result_807_; lean_object* v_cache_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_839_; 
v___x_796_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_671_, v_a_790_, v_cache_673_);
v_result_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_result_797_);
v_cache_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc_ref(v_cache_798_);
lean_dec_ref(v___x_796_);
v_aig_799_ = lean_ctor_get(v_result_797_, 0);
lean_inc_ref(v_aig_799_);
v_ref_800_ = lean_ctor_get(v_result_797_, 1);
lean_inc_ref(v_ref_800_);
lean_dec_ref(v_result_797_);
v___x_801_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_799_, v_a_791_, v_cache_798_);
v_result_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_ref(v_result_802_);
v_cache_803_ = lean_ctor_get(v___x_801_, 1);
lean_inc_ref(v_cache_803_);
lean_dec_ref(v___x_801_);
v_aig_804_ = lean_ctor_get(v_result_802_, 0);
lean_inc_ref(v_aig_804_);
v_ref_805_ = lean_ctor_get(v_result_802_, 1);
lean_inc_ref(v_ref_805_);
lean_dec_ref(v_result_802_);
v___x_806_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_804_, v_a_792_, v_cache_803_);
v_result_807_ = lean_ctor_get(v___x_806_, 0);
v_cache_808_ = lean_ctor_get(v___x_806_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_839_ == 0)
{
v___x_810_ = v___x_806_;
v_isShared_811_ = v_isSharedCheck_839_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_cache_808_);
lean_inc(v_result_807_);
lean_dec(v___x_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_839_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_aig_812_; lean_object* v_ref_813_; lean_object* v_gate_814_; uint8_t v_invert_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_838_; 
v_aig_812_ = lean_ctor_get(v_result_807_, 0);
lean_inc_ref(v_aig_812_);
v_ref_813_ = lean_ctor_get(v_result_807_, 1);
lean_inc_ref(v_ref_813_);
lean_dec_ref(v_result_807_);
v_gate_814_ = lean_ctor_get(v_ref_800_, 0);
v_invert_815_ = lean_ctor_get_uint8(v_ref_800_, sizeof(void*)*1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_ref_800_);
if (v_isSharedCheck_838_ == 0)
{
v___x_817_ = v_ref_800_;
v_isShared_818_ = v_isSharedCheck_838_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_gate_814_);
lean_dec(v_ref_800_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_838_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_gate_819_; uint8_t v_invert_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_837_; 
v_gate_819_ = lean_ctor_get(v_ref_805_, 0);
v_invert_820_ = lean_ctor_get_uint8(v_ref_805_, sizeof(void*)*1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_ref_805_);
if (v_isSharedCheck_837_ == 0)
{
v___x_822_ = v_ref_805_;
v_isShared_823_ = v_isSharedCheck_837_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_gate_819_);
lean_dec(v_ref_805_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_837_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_discrRef_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v_gate_814_);
v_discrRef_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_gate_814_);
v_discrRef_825_ = v_reuseFailAlloc_836_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v_lhsRef_827_; 
lean_ctor_set_uint8(v_discrRef_825_, sizeof(void*)*1, v_invert_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_gate_819_);
v_lhsRef_827_ = v___x_817_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_gate_819_);
v_lhsRef_827_ = v_reuseFailAlloc_835_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v_input_829_; 
lean_ctor_set_uint8(v_lhsRef_827_, sizeof(void*)*1, v_invert_820_);
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 0);
lean_ctor_set(v___x_794_, 2, v_ref_813_);
lean_ctor_set(v___x_794_, 1, v_lhsRef_827_);
lean_ctor_set(v___x_794_, 0, v_discrRef_825_);
v_input_829_ = v___x_794_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_discrRef_825_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_lhsRef_827_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_ref_813_);
v_input_829_ = v_reuseFailAlloc_834_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v_ret_830_; lean_object* v___x_832_; 
v_ret_830_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(v_aig_812_, v_input_829_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_ret_830_);
v___x_832_ = v___x_810_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_ret_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_cache_808_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_m_842_, v_a_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_845_, lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(v_00_u03b2_845_, v_m_846_, v_a_847_);
lean_dec_ref(v_m_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_849_, lean_object* v_m_850_, lean_object* v_a_851_, lean_object* v_b_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_m_850_, v_a_851_, v_b_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_854_, lean_object* v_a_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_858_, lean_object* v_a_859_, lean_object* v_x_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_862_, lean_object* v_a_863_, lean_object* v_x_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_862_, v_a_863_, v_x_864_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_867_, lean_object* v_data_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_870_, lean_object* v_a_871_, lean_object* v_b_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_871_, v_b_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_875_, lean_object* v_i_876_, lean_object* v_source_877_, lean_object* v_target_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_876_, v_source_877_, v_target_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object* v_expr_884_, lean_object* v_aig_885_, lean_object* v_cache_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_885_, v_expr_884_, v_cache_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = lean_unsigned_to_nat(16u);
v___x_894_ = lean_mk_array(v___x_893_, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_899_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_901_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
v___x_903_ = lean_unsigned_to_nat(16u);
v___x_904_ = lean_mk_array(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_result_912_; 
v___x_909_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_910_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_911_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v___x_909_, v_expr_908_, v___x_910_);
v_result_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_result_912_);
lean_dec_ref(v___x_911_);
return v_result_912_;
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
