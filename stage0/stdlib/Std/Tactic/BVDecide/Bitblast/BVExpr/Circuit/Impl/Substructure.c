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
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_a_1_, lean_object* v_b_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_dec(v_b_2_);
lean_dec(v_a_1_);
return v_x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_value_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_19_; 
v_key_4_ = lean_ctor_get(v_x_3_, 0);
v_value_5_ = lean_ctor_get(v_x_3_, 1);
v_tail_6_ = lean_ctor_get(v_x_3_, 2);
v_isSharedCheck_19_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_19_ == 0)
{
v___x_8_ = v_x_3_;
v_isShared_9_ = v_isSharedCheck_19_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_value_5_);
lean_inc(v_key_4_);
lean_dec(v_x_3_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_19_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_1_);
lean_inc(v_key_4_);
v___x_11_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_10_, v_key_4_, v_a_1_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_12_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_1_, v_b_2_, v_tail_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 2, v___x_12_);
v___x_14_ = v___x_8_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_key_4_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v_value_5_);
lean_ctor_set(v_reuseFailAlloc_15_, 2, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
else
{
lean_object* v___x_17_; 
lean_dec(v_value_5_);
lean_dec(v_key_4_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_b_2_);
lean_ctor_set(v___x_8_, 0, v_a_1_);
v___x_17_ = v___x_8_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_1_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_b_2_);
lean_ctor_set(v_reuseFailAlloc_18_, 2, v_tail_6_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
uint8_t v___x_22_; 
lean_dec(v_a_20_);
v___x_22_ = 0;
return v___x_22_;
}
else
{
lean_object* v_key_23_; lean_object* v_tail_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_key_23_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_key_23_);
v_tail_24_ = lean_ctor_get(v_x_21_, 2);
lean_inc(v_tail_24_);
lean_dec_ref_known(v_x_21_, 3);
v___x_25_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_20_);
v___x_26_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_25_, v_key_23_, v_a_20_);
if (v___x_26_ == 0)
{
v_x_21_ = v_tail_24_;
goto _start;
}
else
{
lean_dec(v_tail_24_);
lean_dec(v_a_20_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_a_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_28_, v_x_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_32_){
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_x_45_){
_start:
{
uint64_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_x_45_);
lean_dec(v_x_45_);
v_r_47_ = lean_box_uint64(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_x_48_, lean_object* v_x_49_){
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
v___x_57_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_key_50_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object* v_i_76_, lean_object* v_source_77_, lean_object* v_target_78_){
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
v_target_84_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_target_78_, v_es_81_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_data_88_){
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
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v___x_92_, v_data_88_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
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
v___x_106_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_98_);
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
v___x_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_98_, v_bkt_118_);
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
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_buckets_x27_123_);
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
v___x_139_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_98_, v_b_99_, v_bkt_118_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object* v_aig_145_, lean_object* v_ref_146_){
_start:
{
lean_object* v_gate_147_; uint8_t v_invert_148_; lean_object* v_decls_149_; lean_object* v_decl_150_; 
v_gate_147_ = lean_ctor_get(v_ref_146_, 0);
v_invert_148_ = lean_ctor_get_uint8(v_ref_146_, sizeof(void*)*1);
v_decls_149_ = lean_ctor_get(v_aig_145_, 0);
v_decl_150_ = lean_array_fget_borrowed(v_decls_149_, v_gate_147_);
if (lean_obj_tag(v_decl_150_) == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(v_invert_148_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object* v_aig_154_, lean_object* v_ref_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v_aig_154_, v_ref_155_);
lean_dec_ref(v_ref_155_);
lean_dec_ref(v_aig_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_a_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_a_157_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_key_160_; lean_object* v_value_161_; lean_object* v_tail_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_key_160_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_key_160_);
v_value_161_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_value_161_);
v_tail_162_ = lean_ctor_get(v_x_158_, 2);
lean_inc(v_tail_162_);
lean_dec_ref_known(v_x_158_, 3);
v___x_163_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_157_);
v___x_164_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_163_, v_key_160_, v_a_157_);
if (v___x_164_ == 0)
{
lean_dec(v_value_161_);
v_x_158_ = v_tail_162_;
goto _start;
}
else
{
lean_object* v___x_166_; 
lean_dec(v_tail_162_);
lean_dec(v_a_157_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v_value_161_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_buckets_169_; lean_object* v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v_fold_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_buckets_169_ = lean_ctor_get(v_m_167_, 1);
v___x_170_ = lean_array_get_size(v_buckets_169_);
v___x_171_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_168_);
v___x_172_ = 32ULL;
v___x_173_ = lean_uint64_shift_right(v___x_171_, v___x_172_);
v_fold_174_ = lean_uint64_xor(v___x_171_, v___x_173_);
v___x_175_ = 16ULL;
v___x_176_ = lean_uint64_shift_right(v_fold_174_, v___x_175_);
v___x_177_ = lean_uint64_xor(v_fold_174_, v___x_176_);
v___x_178_ = lean_uint64_to_usize(v___x_177_);
v___x_179_ = lean_usize_of_nat(v___x_170_);
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_sub(v___x_179_, v___x_180_);
v___x_182_ = lean_usize_land(v___x_178_, v___x_181_);
v___x_183_ = lean_array_uget_borrowed(v_buckets_169_, v___x_182_);
lean_inc(v___x_183_);
v___x_184_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_168_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_185_, v_a_186_);
lean_dec_ref(v_m_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object* v_aig_191_, lean_object* v_input_192_){
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
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_cache_199_, v_decl_215_);
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
v_lhsVal_234_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_218_, v_lhs_193_);
lean_dec_ref(v_lhs_193_);
v_rhsVal_235_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_218_, v_rhs_194_);
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
v_ref_232_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0));
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
v_cache_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_cache_199_, v_decl_215_, v_g_250_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object* v_aig_278_, lean_object* v_input_279_){
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
v___x_290_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_278_, v___x_289_);
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
v___x_294_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_278_, v___x_293_);
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object* v_aig_297_, lean_object* v_input_298_){
_start:
{
lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v_lhs_305_; lean_object* v_rhs_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_419_; 
v_lhs_305_ = lean_ctor_get(v_input_298_, 0);
v_rhs_306_ = lean_ctor_get(v_input_298_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_input_298_);
if (v_isSharedCheck_419_ == 0)
{
v___x_308_ = v_input_298_;
v_isShared_309_ = v_isSharedCheck_419_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_rhs_306_);
lean_inc(v_lhs_305_);
lean_dec(v_input_298_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_419_;
goto v_resetjp_307_;
}
v___jp_299_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___y_301_);
lean_ctor_set(v___x_303_, 1, v___y_302_);
v___x_304_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_300_, v___x_303_);
return v___x_304_;
}
v_resetjp_307_:
{
lean_object* v_gate_310_; uint8_t v_invert_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_418_; 
v_gate_310_ = lean_ctor_get(v_lhs_305_, 0);
v_invert_311_ = lean_ctor_get_uint8(v_lhs_305_, sizeof(void*)*1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_lhs_305_);
if (v_isSharedCheck_418_ == 0)
{
v___x_313_ = v_lhs_305_;
v_isShared_314_ = v_isSharedCheck_418_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_gate_310_);
lean_dec(v_lhs_305_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_418_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_365_; uint8_t v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_383_; lean_object* v___y_408_; 
v___x_315_ = 0;
v___x_316_ = 1;
if (v_invert_311_ == 0)
{
lean_object* v___x_416_; 
lean_inc(v_gate_310_);
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v_gate_310_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_315_);
v___y_408_ = v___x_416_;
goto v___jp_407_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_gate_310_);
v___x_417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_417_, 0, v_gate_310_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_316_);
v___y_408_ = v___x_417_;
goto v___jp_407_;
}
v___jp_317_:
{
uint8_t v_invert_321_; 
v_invert_321_ = lean_ctor_get_uint8(v___y_319_, sizeof(void*)*1);
if (v_invert_321_ == 0)
{
lean_object* v_gate_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_gate_322_ = lean_ctor_get(v___y_319_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___y_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___y_319_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_gate_322_);
lean_dec(v___y_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_gate_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_316_);
v___y_300_ = v___y_318_;
v___y_301_ = v___y_320_;
v___y_302_ = v___x_327_;
goto v___jp_299_;
}
}
}
else
{
lean_object* v_gate_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_gate_330_ = lean_ctor_get(v___y_319_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___y_319_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___y_319_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_gate_330_);
lean_dec(v___y_319_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_gate_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_315_);
v___y_300_ = v___y_318_;
v___y_301_ = v___y_320_;
v___y_302_ = v___x_335_;
goto v___jp_299_;
}
}
}
}
v___jp_338_:
{
lean_object* v_res_342_; uint8_t v_invert_343_; 
v_res_342_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_339_, v___y_341_);
v_invert_343_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*1);
if (v_invert_343_ == 0)
{
lean_object* v_aig_344_; lean_object* v_ref_345_; lean_object* v_gate_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_aig_344_ = lean_ctor_get(v_res_342_, 0);
lean_inc_ref(v_aig_344_);
v_ref_345_ = lean_ctor_get(v_res_342_, 1);
lean_inc_ref(v_ref_345_);
lean_dec_ref(v_res_342_);
v_gate_346_ = lean_ctor_get(v___y_340_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___y_340_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_gate_346_);
lean_dec(v___y_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_gate_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_316_);
v___y_318_ = v_aig_344_;
v___y_319_ = v_ref_345_;
v___y_320_ = v___x_351_;
goto v___jp_317_;
}
}
}
else
{
lean_object* v_aig_354_; lean_object* v_ref_355_; lean_object* v_gate_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_aig_354_ = lean_ctor_get(v_res_342_, 0);
lean_inc_ref(v_aig_354_);
v_ref_355_ = lean_ctor_get(v_res_342_, 1);
lean_inc_ref(v_ref_355_);
lean_dec_ref(v_res_342_);
v_gate_356_ = lean_ctor_get(v___y_340_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___y_340_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_gate_356_);
lean_dec(v___y_340_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_gate_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_315_);
v___y_318_ = v_aig_354_;
v___y_319_ = v_ref_355_;
v___y_320_ = v___x_361_;
goto v___jp_317_;
}
}
}
}
v___jp_364_:
{
if (v___y_366_ == 0)
{
lean_object* v___x_371_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___y_368_);
v___x_371_ = v___x_313_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___y_368_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_315_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_371_);
lean_ctor_set(v___x_308_, 0, v___y_369_);
v___x_373_ = v___x_308_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___y_369_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v___y_339_ = v___y_365_;
v___y_340_ = v___y_367_;
v___y_341_ = v___x_373_;
goto v___jp_338_;
}
}
}
else
{
lean_object* v___x_377_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___y_368_);
v___x_377_ = v___x_313_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___y_368_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_316_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_377_);
lean_ctor_set(v___x_308_, 0, v___y_369_);
v___x_379_ = v___x_308_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___y_369_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v___y_339_ = v___y_365_;
v___y_340_ = v___y_367_;
v___y_341_ = v___x_379_;
goto v___jp_338_;
}
}
}
}
v___jp_382_:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_297_, v___y_383_);
if (v_invert_311_ == 0)
{
lean_object* v_aig_385_; lean_object* v_ref_386_; lean_object* v_gate_387_; uint8_t v_invert_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_aig_385_ = lean_ctor_get(v_res_384_, 0);
lean_inc_ref(v_aig_385_);
v_ref_386_ = lean_ctor_get(v_res_384_, 1);
lean_inc_ref(v_ref_386_);
lean_dec_ref(v_res_384_);
v_gate_387_ = lean_ctor_get(v_rhs_306_, 0);
v_invert_388_ = lean_ctor_get_uint8(v_rhs_306_, sizeof(void*)*1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_rhs_306_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v_rhs_306_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_gate_387_);
lean_dec(v_rhs_306_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v_gate_310_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_gate_310_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*1, v___x_316_);
v___y_365_ = v_aig_385_;
v___y_366_ = v_invert_388_;
v___y_367_ = v_ref_386_;
v___y_368_ = v_gate_387_;
v___y_369_ = v___x_393_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v_aig_396_; lean_object* v_ref_397_; lean_object* v_gate_398_; uint8_t v_invert_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_aig_396_ = lean_ctor_get(v_res_384_, 0);
lean_inc_ref(v_aig_396_);
v_ref_397_ = lean_ctor_get(v_res_384_, 1);
lean_inc_ref(v_ref_397_);
lean_dec_ref(v_res_384_);
v_gate_398_ = lean_ctor_get(v_rhs_306_, 0);
v_invert_399_ = lean_ctor_get_uint8(v_rhs_306_, sizeof(void*)*1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_rhs_306_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v_rhs_306_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_gate_398_);
lean_dec(v_rhs_306_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_gate_310_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_gate_310_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1, v___x_315_);
v___y_365_ = v_aig_396_;
v___y_366_ = v_invert_399_;
v___y_367_ = v_ref_397_;
v___y_368_ = v_gate_398_;
v___y_369_ = v___x_404_;
goto v___jp_364_;
}
}
}
}
v___jp_407_:
{
uint8_t v_invert_409_; 
v_invert_409_ = lean_ctor_get_uint8(v_rhs_306_, sizeof(void*)*1);
if (v_invert_409_ == 0)
{
lean_object* v_gate_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_gate_410_ = lean_ctor_get(v_rhs_306_, 0);
lean_inc(v_gate_410_);
v___x_411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_411_, 0, v_gate_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_316_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___y_408_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___y_383_ = v___x_412_;
goto v___jp_382_;
}
else
{
lean_object* v_gate_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_gate_413_ = lean_ctor_get(v_rhs_306_, 0);
lean_inc(v_gate_413_);
v___x_414_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_414_, 0, v_gate_413_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*1, v___x_315_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___y_408_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___y_383_ = v___x_415_;
goto v___jp_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* v_aig_420_, lean_object* v_input_421_){
_start:
{
lean_object* v___y_423_; lean_object* v_lhs_463_; lean_object* v_rhs_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_508_; 
v_lhs_463_ = lean_ctor_get(v_input_421_, 0);
v_rhs_464_ = lean_ctor_get(v_input_421_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_input_421_);
if (v_isSharedCheck_508_ == 0)
{
v___x_466_ = v_input_421_;
v_isShared_467_ = v_isSharedCheck_508_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_rhs_464_);
lean_inc(v_lhs_463_);
lean_dec(v_input_421_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_508_;
goto v_resetjp_465_;
}
v___jp_422_:
{
lean_object* v_res_424_; lean_object* v_ref_425_; uint8_t v_invert_426_; 
v_res_424_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_420_, v___y_423_);
v_ref_425_ = lean_ctor_get(v_res_424_, 1);
lean_inc_ref(v_ref_425_);
v_invert_426_ = lean_ctor_get_uint8(v_ref_425_, sizeof(void*)*1);
if (v_invert_426_ == 0)
{
lean_object* v_aig_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_443_; 
v_aig_427_ = lean_ctor_get(v_res_424_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_res_424_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v_res_424_, 1);
lean_dec(v_unused_444_);
v___x_429_ = v_res_424_;
v_isShared_430_ = v_isSharedCheck_443_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_aig_427_);
lean_dec(v_res_424_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_443_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_gate_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_442_; 
v_gate_431_ = lean_ctor_get(v_ref_425_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_ref_425_);
if (v_isSharedCheck_442_ == 0)
{
v___x_433_ = v_ref_425_;
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_gate_431_);
lean_dec(v_ref_425_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___x_435_; lean_object* v___x_437_; 
v___x_435_ = 1;
if (v_isShared_434_ == 0)
{
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_gate_431_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*1, v___x_435_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_437_);
v___x_439_ = v___x_429_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_aig_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
lean_object* v_aig_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_461_; 
v_aig_445_ = lean_ctor_get(v_res_424_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_res_424_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_res_424_, 1);
lean_dec(v_unused_462_);
v___x_447_ = v_res_424_;
v_isShared_448_ = v_isSharedCheck_461_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_aig_445_);
lean_dec(v_res_424_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_461_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_gate_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_gate_449_ = lean_ctor_get(v_ref_425_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_ref_425_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v_ref_425_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_gate_449_);
lean_dec(v_ref_425_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; lean_object* v___x_455_; 
v___x_453_ = 0;
if (v_isShared_452_ == 0)
{
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_gate_449_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*1, v___x_453_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_455_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_aig_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
v_resetjp_465_:
{
lean_object* v_gate_468_; uint8_t v_invert_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_507_; 
v_gate_468_ = lean_ctor_get(v_lhs_463_, 0);
v_invert_469_ = lean_ctor_get_uint8(v_lhs_463_, sizeof(void*)*1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_lhs_463_);
if (v_isSharedCheck_507_ == 0)
{
v___x_471_ = v_lhs_463_;
v_isShared_472_ = v_isSharedCheck_507_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_gate_468_);
lean_dec(v_lhs_463_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_507_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; lean_object* v___y_475_; 
v___x_473_ = 1;
if (v_invert_469_ == 0)
{
lean_object* v___x_501_; 
if (v_isShared_472_ == 0)
{
v___x_501_ = v___x_471_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_gate_468_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_473_);
v___y_475_ = v___x_501_;
goto v___jp_474_;
}
}
else
{
uint8_t v___x_503_; lean_object* v___x_505_; 
v___x_503_ = 0;
if (v_isShared_472_ == 0)
{
v___x_505_ = v___x_471_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_gate_468_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*1, v___x_503_);
v___y_475_ = v___x_505_;
goto v___jp_474_;
}
}
v___jp_474_:
{
uint8_t v_invert_476_; 
v_invert_476_ = lean_ctor_get_uint8(v_rhs_464_, sizeof(void*)*1);
if (v_invert_476_ == 0)
{
lean_object* v_gate_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_gate_477_ = lean_ctor_get(v_rhs_464_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_rhs_464_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v_rhs_464_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_gate_477_);
lean_dec(v_rhs_464_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_gate_477_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1, v___x_473_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_482_);
lean_ctor_set(v___x_466_, 0, v___y_475_);
v___x_484_ = v___x_466_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___y_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v___y_423_ = v___x_484_;
goto v___jp_422_;
}
}
}
}
else
{
lean_object* v_gate_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_499_; 
v_gate_488_ = lean_ctor_get(v_rhs_464_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_rhs_464_);
if (v_isSharedCheck_499_ == 0)
{
v___x_490_ = v_rhs_464_;
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_gate_488_);
lean_dec(v_rhs_464_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; lean_object* v___x_494_; 
v___x_492_ = 0;
if (v_isShared_491_ == 0)
{
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_gate_488_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*1, v___x_492_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_494_);
lean_ctor_set(v___x_466_, 0, v___y_475_);
v___x_496_ = v___x_466_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___y_475_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
v___y_423_ = v___x_496_;
goto v___jp_422_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* v_aig_509_, lean_object* v_input_510_){
_start:
{
lean_object* v_discr_511_; lean_object* v_lhs_512_; lean_object* v_rhs_513_; lean_object* v___x_514_; lean_object* v_res_515_; lean_object* v_aig_516_; lean_object* v_ref_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_570_; 
v_discr_511_ = lean_ctor_get(v_input_510_, 0);
lean_inc_ref_n(v_discr_511_, 2);
v_lhs_512_ = lean_ctor_get(v_input_510_, 1);
lean_inc_ref(v_lhs_512_);
v_rhs_513_ = lean_ctor_get(v_input_510_, 2);
lean_inc_ref(v_rhs_513_);
lean_dec_ref(v_input_510_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_discr_511_);
lean_ctor_set(v___x_514_, 1, v_lhs_512_);
v_res_515_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_509_, v___x_514_);
v_aig_516_ = lean_ctor_get(v_res_515_, 0);
v_ref_517_ = lean_ctor_get(v_res_515_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_res_515_);
if (v_isSharedCheck_570_ == 0)
{
v___x_519_ = v_res_515_;
v_isShared_520_ = v_isSharedCheck_570_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_ref_517_);
lean_inc(v_aig_516_);
lean_dec(v_res_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_570_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_gate_521_; uint8_t v_invert_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_569_; 
v_gate_521_ = lean_ctor_get(v_discr_511_, 0);
v_invert_522_ = lean_ctor_get_uint8(v_discr_511_, sizeof(void*)*1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_discr_511_);
if (v_isSharedCheck_569_ == 0)
{
v___x_524_ = v_discr_511_;
v_isShared_525_ = v_isSharedCheck_569_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_gate_521_);
lean_dec(v_discr_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_569_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_gate_526_; uint8_t v_invert_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_568_; 
v_gate_526_ = lean_ctor_get(v_rhs_513_, 0);
v_invert_527_ = lean_ctor_get_uint8(v_rhs_513_, sizeof(void*)*1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_rhs_513_);
if (v_isSharedCheck_568_ == 0)
{
v___x_529_ = v_rhs_513_;
v_isShared_530_ = v_isSharedCheck_568_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_gate_526_);
lean_dec(v_rhs_513_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_568_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_aig_532_; lean_object* v_ref_533_; 
if (v_invert_522_ == 0)
{
uint8_t v___x_560_; lean_object* v___x_562_; 
v___x_560_ = 1;
if (v_isShared_525_ == 0)
{
v___x_562_ = v___x_524_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_gate_521_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_560_);
v_aig_532_ = v_aig_516_;
v_ref_533_ = v___x_562_;
goto v___jp_531_;
}
}
else
{
uint8_t v___x_564_; lean_object* v___x_566_; 
v___x_564_ = 0;
if (v_isShared_525_ == 0)
{
v___x_566_ = v___x_524_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_gate_521_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_564_);
v_aig_532_ = v_aig_516_;
v_ref_533_ = v___x_566_;
goto v___jp_531_;
}
}
v___jp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_530_ == 0)
{
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_gate_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_559_, sizeof(void*)*1, v_invert_527_);
v___x_535_ = v_reuseFailAlloc_559_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_535_);
lean_ctor_set(v___x_519_, 0, v_ref_533_);
v___x_537_ = v___x_519_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_ref_533_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_558_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v_res_538_; lean_object* v_aig_539_; lean_object* v_ref_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_557_; 
v_res_538_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_532_, v___x_537_);
v_aig_539_ = lean_ctor_get(v_res_538_, 0);
v_ref_540_ = lean_ctor_get(v_res_538_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_res_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_542_ = v_res_538_;
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_ref_540_);
lean_inc(v_aig_539_);
lean_dec(v_res_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_gate_544_; uint8_t v_invert_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_gate_544_ = lean_ctor_get(v_ref_517_, 0);
v_invert_545_ = lean_ctor_get_uint8(v_ref_517_, sizeof(void*)*1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_ref_517_);
if (v_isSharedCheck_556_ == 0)
{
v___x_547_ = v_ref_517_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_gate_544_);
lean_dec(v_ref_517_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_lhsRef_550_; 
if (v_isShared_548_ == 0)
{
v_lhsRef_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*1, v_invert_545_);
v_lhsRef_550_ = v_reuseFailAlloc_555_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_lhsRef_550_);
v___x_552_ = v___x_542_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_lhsRef_550_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_ref_540_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_539_, v___x_552_);
return v___x_553_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* v_aig_571_, lean_object* v_input_572_){
_start:
{
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v_res_602_; lean_object* v_aig_603_; lean_object* v_ref_604_; lean_object* v___y_606_; lean_object* v_lhs_631_; lean_object* v_rhs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_671_; 
lean_inc_ref(v_input_572_);
v_res_602_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_571_, v_input_572_);
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
lean_ctor_set(v___x_577_, 0, v___y_574_);
lean_ctor_set(v___x_577_, 1, v___y_576_);
v___x_578_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_575_, v___x_577_);
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
v___y_574_ = v___y_582_;
v___y_575_ = v___y_581_;
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
v___y_574_ = v___y_582_;
v___y_575_ = v___y_581_;
v___y_576_ = v___x_599_;
goto v___jp_573_;
}
}
}
}
v___jp_605_:
{
lean_object* v_res_607_; uint8_t v_invert_608_; 
v_res_607_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_603_, v___y_606_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* v_aig_672_, lean_object* v_expr_673_, lean_object* v_cache_674_){
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
v___x_684_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_672_, v_a_683_, v_cache_674_);
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
v___x_745_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_672_, v_a_743_, v_cache_674_);
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
v___x_750_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_748_, v_a_744_, v_cache_747_);
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
v_ret_770_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_756_, v_input_769_);
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
v_ret_774_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_756_, v_input_769_);
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
v_ret_778_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_756_, v_input_769_);
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
v_ret_782_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_756_, v_input_769_);
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
v___x_797_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_672_, v_a_791_, v_cache_674_);
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
v___x_802_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_800_, v_a_792_, v_cache_799_);
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
v___x_807_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_805_, v_a_793_, v_cache_804_);
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
v_ret_831_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_813_, v_input_830_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_842_, lean_object* v_m_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_843_, v_a_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_846_, v_m_847_, v_a_848_);
lean_dec_ref(v_m_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_850_, lean_object* v_m_851_, lean_object* v_a_852_, lean_object* v_b_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_851_, v_a_852_, v_b_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_855_, lean_object* v_a_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_859_, lean_object* v_a_860_, lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_863_, lean_object* v_a_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_863_, v_a_864_, v_x_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_868_, lean_object* v_data_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_871_, lean_object* v_a_872_, lean_object* v_b_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_872_, v_b_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_876_, lean_object* v_i_877_, lean_object* v_source_878_, lean_object* v_target_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_877_, v_source_878_, v_target_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_882_, v_x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_unsigned_to_nat(16u);
v___x_891_ = lean_mk_array(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_896_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_898_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = lean_mk_array(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_result_909_; 
v___x_906_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_907_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_908_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_906_, v_expr_905_, v___x_907_);
v_result_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_result_909_);
lean_dec_ref(v___x_908_);
return v_result_909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* v_expr_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_, lean_object* v_h__3_913_, lean_object* v_h__4_914_, lean_object* v_h__5_915_){
_start:
{
switch(lean_obj_tag(v_expr_910_))
{
case 0:
{
lean_object* v_a_916_; lean_object* v___x_917_; 
lean_dec(v_h__5_915_);
lean_dec(v_h__4_914_);
lean_dec(v_h__3_913_);
lean_dec(v_h__2_912_);
v_a_916_ = lean_ctor_get(v_expr_910_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v_expr_910_, 1);
v___x_917_ = lean_apply_1(v_h__1_911_, v_a_916_);
return v___x_917_;
}
case 1:
{
uint8_t v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_h__5_915_);
lean_dec(v_h__4_914_);
lean_dec(v_h__3_913_);
lean_dec(v_h__1_911_);
v_a_918_ = lean_ctor_get_uint8(v_expr_910_, 0);
lean_dec_ref_known(v_expr_910_, 0);
v___x_919_ = lean_box(v_a_918_);
v___x_920_ = lean_apply_1(v_h__2_912_, v___x_919_);
return v___x_920_;
}
case 2:
{
lean_object* v_a_921_; lean_object* v___x_922_; 
lean_dec(v_h__5_915_);
lean_dec(v_h__4_914_);
lean_dec(v_h__2_912_);
lean_dec(v_h__1_911_);
v_a_921_ = lean_ctor_get(v_expr_910_, 0);
lean_inc_ref(v_a_921_);
lean_dec_ref_known(v_expr_910_, 1);
v___x_922_ = lean_apply_1(v_h__3_913_, v_a_921_);
return v___x_922_;
}
case 3:
{
uint8_t v_a_923_; lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_h__4_914_);
lean_dec(v_h__3_913_);
lean_dec(v_h__2_912_);
lean_dec(v_h__1_911_);
v_a_923_ = lean_ctor_get_uint8(v_expr_910_, sizeof(void*)*2);
v_a_924_ = lean_ctor_get(v_expr_910_, 0);
lean_inc_ref(v_a_924_);
v_a_925_ = lean_ctor_get(v_expr_910_, 1);
lean_inc_ref(v_a_925_);
lean_dec_ref_known(v_expr_910_, 2);
v___x_926_ = lean_box(v_a_923_);
v___x_927_ = lean_apply_3(v_h__5_915_, v___x_926_, v_a_924_, v_a_925_);
return v___x_927_;
}
default: 
{
lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v_a_930_; lean_object* v___x_931_; 
lean_dec(v_h__5_915_);
lean_dec(v_h__3_913_);
lean_dec(v_h__2_912_);
lean_dec(v_h__1_911_);
v_a_928_ = lean_ctor_get(v_expr_910_, 0);
lean_inc_ref(v_a_928_);
v_a_929_ = lean_ctor_get(v_expr_910_, 1);
lean_inc_ref(v_a_929_);
v_a_930_ = lean_ctor_get(v_expr_910_, 2);
lean_inc_ref(v_a_930_);
lean_dec_ref_known(v_expr_910_, 3);
v___x_931_ = lean_apply_3(v_h__4_914_, v_a_928_, v_a_929_, v_a_930_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* v_motive_932_, lean_object* v_expr_933_, lean_object* v_h__1_934_, lean_object* v_h__2_935_, lean_object* v_h__3_936_, lean_object* v_h__4_937_, lean_object* v_h__5_938_){
_start:
{
switch(lean_obj_tag(v_expr_933_))
{
case 0:
{
lean_object* v_a_939_; lean_object* v___x_940_; 
lean_dec(v_h__5_938_);
lean_dec(v_h__4_937_);
lean_dec(v_h__3_936_);
lean_dec(v_h__2_935_);
v_a_939_ = lean_ctor_get(v_expr_933_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v_expr_933_, 1);
v___x_940_ = lean_apply_1(v_h__1_934_, v_a_939_);
return v___x_940_;
}
case 1:
{
uint8_t v_a_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_h__5_938_);
lean_dec(v_h__4_937_);
lean_dec(v_h__3_936_);
lean_dec(v_h__1_934_);
v_a_941_ = lean_ctor_get_uint8(v_expr_933_, 0);
lean_dec_ref_known(v_expr_933_, 0);
v___x_942_ = lean_box(v_a_941_);
v___x_943_ = lean_apply_1(v_h__2_935_, v___x_942_);
return v___x_943_;
}
case 2:
{
lean_object* v_a_944_; lean_object* v___x_945_; 
lean_dec(v_h__5_938_);
lean_dec(v_h__4_937_);
lean_dec(v_h__2_935_);
lean_dec(v_h__1_934_);
v_a_944_ = lean_ctor_get(v_expr_933_, 0);
lean_inc_ref(v_a_944_);
lean_dec_ref_known(v_expr_933_, 1);
v___x_945_ = lean_apply_1(v_h__3_936_, v_a_944_);
return v___x_945_;
}
case 3:
{
uint8_t v_a_946_; lean_object* v_a_947_; lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_h__4_937_);
lean_dec(v_h__3_936_);
lean_dec(v_h__2_935_);
lean_dec(v_h__1_934_);
v_a_946_ = lean_ctor_get_uint8(v_expr_933_, sizeof(void*)*2);
v_a_947_ = lean_ctor_get(v_expr_933_, 0);
lean_inc_ref(v_a_947_);
v_a_948_ = lean_ctor_get(v_expr_933_, 1);
lean_inc_ref(v_a_948_);
lean_dec_ref_known(v_expr_933_, 2);
v___x_949_ = lean_box(v_a_946_);
v___x_950_ = lean_apply_3(v_h__5_938_, v___x_949_, v_a_947_, v_a_948_);
return v___x_950_;
}
default: 
{
lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_954_; 
lean_dec(v_h__5_938_);
lean_dec(v_h__3_936_);
lean_dec(v_h__2_935_);
lean_dec(v_h__1_934_);
v_a_951_ = lean_ctor_get(v_expr_933_, 0);
lean_inc_ref(v_a_951_);
v_a_952_ = lean_ctor_get(v_expr_933_, 1);
lean_inc_ref(v_a_952_);
v_a_953_ = lean_ctor_get(v_expr_933_, 2);
lean_inc_ref(v_a_953_);
lean_dec_ref_known(v_expr_933_, 3);
v___x_954_ = lean_apply_3(v_h__4_937_, v_a_951_, v_a_952_, v_a_953_);
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* v_x_955_, lean_object* v_h__1_956_){
_start:
{
lean_object* v_result_957_; lean_object* v_cache_958_; lean_object* v_aig_959_; lean_object* v_ref_960_; lean_object* v___x_961_; 
v_result_957_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_result_957_);
v_cache_958_ = lean_ctor_get(v_x_955_, 1);
lean_inc_ref(v_cache_958_);
lean_dec_ref(v_x_955_);
v_aig_959_ = lean_ctor_get(v_result_957_, 0);
lean_inc_ref(v_aig_959_);
v_ref_960_ = lean_ctor_get(v_result_957_, 1);
lean_inc_ref(v_ref_960_);
lean_dec_ref(v_result_957_);
v___x_961_ = lean_apply_4(v_h__1_956_, v_aig_959_, v_ref_960_, lean_box(0), v_cache_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* v_aig_962_, lean_object* v_motive_963_, lean_object* v_x_964_, lean_object* v_h__1_965_){
_start:
{
lean_object* v_result_966_; lean_object* v_cache_967_; lean_object* v_aig_968_; lean_object* v_ref_969_; lean_object* v___x_970_; 
v_result_966_ = lean_ctor_get(v_x_964_, 0);
lean_inc_ref(v_result_966_);
v_cache_967_ = lean_ctor_get(v_x_964_, 1);
lean_inc_ref(v_cache_967_);
lean_dec_ref(v_x_964_);
v_aig_968_ = lean_ctor_get(v_result_966_, 0);
lean_inc_ref(v_aig_968_);
v_ref_969_ = lean_ctor_get(v_result_966_, 1);
lean_inc_ref(v_ref_969_);
lean_dec_ref(v_result_966_);
v___x_970_ = lean_apply_4(v_h__1_965_, v_aig_968_, v_ref_969_, lean_box(0), v_cache_967_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* v_aig_971_, lean_object* v_motive_972_, lean_object* v_x_973_, lean_object* v_h__1_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_971_, v_motive_972_, v_x_973_, v_h__1_974_);
lean_dec_ref(v_aig_971_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t v_g_976_, lean_object* v_h__1_977_, lean_object* v_h__2_978_, lean_object* v_h__3_979_, lean_object* v_h__4_980_){
_start:
{
switch(v_g_976_)
{
case 0:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v_h__4_980_);
lean_dec(v_h__3_979_);
lean_dec(v_h__2_978_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_apply_1(v_h__1_977_, v___x_981_);
return v___x_982_;
}
case 1:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_h__4_980_);
lean_dec(v_h__3_979_);
lean_dec(v_h__1_977_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_apply_1(v_h__2_978_, v___x_983_);
return v___x_984_;
}
case 2:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_h__4_980_);
lean_dec(v_h__2_978_);
lean_dec(v_h__1_977_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_apply_1(v_h__3_979_, v___x_985_);
return v___x_986_;
}
default: 
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_h__3_979_);
lean_dec(v_h__2_978_);
lean_dec(v_h__1_977_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v_h__4_980_, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* v_g_989_, lean_object* v_h__1_990_, lean_object* v_h__2_991_, lean_object* v_h__3_992_, lean_object* v_h__4_993_){
_start:
{
uint8_t v_g_42__boxed_994_; lean_object* v_res_995_; 
v_g_42__boxed_994_ = lean_unbox(v_g_989_);
v_res_995_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_42__boxed_994_, v_h__1_990_, v_h__2_991_, v_h__3_992_, v_h__4_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* v_motive_996_, uint8_t v_g_997_, lean_object* v_h__1_998_, lean_object* v_h__2_999_, lean_object* v_h__3_1000_, lean_object* v_h__4_1001_){
_start:
{
switch(v_g_997_)
{
case 0:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__2_999_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_h__1_998_, v___x_1002_);
return v___x_1003_;
}
case 1:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__1_998_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_apply_1(v_h__2_999_, v___x_1004_);
return v___x_1005_;
}
case 2:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__4_1001_);
lean_dec(v_h__2_999_);
lean_dec(v_h__1_998_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_apply_1(v_h__3_1000_, v___x_1006_);
return v___x_1007_;
}
default: 
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__3_1000_);
lean_dec(v_h__2_999_);
lean_dec(v_h__1_998_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_apply_1(v_h__4_1001_, v___x_1008_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* v_motive_1010_, lean_object* v_g_1011_, lean_object* v_h__1_1012_, lean_object* v_h__2_1013_, lean_object* v_h__3_1014_, lean_object* v_h__4_1015_){
_start:
{
uint8_t v_g_61__boxed_1016_; lean_object* v_res_1017_; 
v_g_61__boxed_1016_ = lean_unbox(v_g_1011_);
v_res_1017_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_1010_, v_g_61__boxed_1016_, v_h__1_1012_, v_h__2_1013_, v_h__3_1014_, v_h__4_1015_);
return v_res_1017_;
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
