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
lean_dec_ref(v_x_21_);
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
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_nbuckets_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_89_ = lean_array_get_size(v_data_88_);
v___x_90_ = lean_unsigned_to_nat(2u);
v_nbuckets_91_ = lean_nat_mul(v___x_89_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v_nbuckets_91_, v___x_93_);
v___x_95_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v___x_92_, v_data_88_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object* v_m_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_size_99_; lean_object* v_buckets_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_143_; 
v_size_99_ = lean_ctor_get(v_m_96_, 0);
v_buckets_100_ = lean_ctor_get(v_m_96_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_m_96_);
if (v_isSharedCheck_143_ == 0)
{
v___x_102_ = v_m_96_;
v_isShared_103_ = v_isSharedCheck_143_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_buckets_100_);
lean_inc(v_size_99_);
lean_dec(v_m_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_143_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v_fold_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; lean_object* v_bkt_117_; uint8_t v___x_118_; 
v___x_104_ = lean_array_get_size(v_buckets_100_);
v___x_105_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_97_);
v___x_106_ = 32ULL;
v___x_107_ = lean_uint64_shift_right(v___x_105_, v___x_106_);
v_fold_108_ = lean_uint64_xor(v___x_105_, v___x_107_);
v___x_109_ = 16ULL;
v___x_110_ = lean_uint64_shift_right(v_fold_108_, v___x_109_);
v___x_111_ = lean_uint64_xor(v_fold_108_, v___x_110_);
v___x_112_ = lean_uint64_to_usize(v___x_111_);
v___x_113_ = lean_usize_of_nat(v___x_104_);
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_sub(v___x_113_, v___x_114_);
v___x_116_ = lean_usize_land(v___x_112_, v___x_115_);
v_bkt_117_ = lean_array_uget_borrowed(v_buckets_100_, v___x_116_);
lean_inc(v_bkt_117_);
lean_inc(v_a_97_);
v___x_118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_97_, v_bkt_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v_size_x27_120_; lean_object* v___x_121_; lean_object* v_buckets_x27_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v_size_x27_120_ = lean_nat_add(v_size_99_, v___x_119_);
lean_dec(v_size_99_);
lean_inc(v_bkt_117_);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v_a_97_);
lean_ctor_set(v___x_121_, 1, v_b_98_);
lean_ctor_set(v___x_121_, 2, v_bkt_117_);
v_buckets_x27_122_ = lean_array_uset(v_buckets_100_, v___x_116_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(4u);
v___x_124_ = lean_nat_mul(v_size_x27_120_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_nat_div(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_array_get_size(v_buckets_x27_122_);
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v_val_129_; lean_object* v___x_131_; 
v_val_129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_buckets_x27_122_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_val_129_);
lean_ctor_set(v___x_102_, 0, v_size_x27_120_);
v___x_131_ = v___x_102_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_val_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_134_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_buckets_x27_122_);
lean_ctor_set(v___x_102_, 0, v_size_x27_120_);
v___x_134_ = v___x_102_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_buckets_x27_122_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v___x_136_; lean_object* v_buckets_x27_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_bkt_117_);
v___x_136_ = lean_box(0);
v_buckets_x27_137_ = lean_array_uset(v_buckets_100_, v___x_116_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_97_, v_b_98_, v_bkt_117_);
v___x_139_ = lean_array_uset(v_buckets_x27_137_, v___x_116_, v___x_138_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_139_);
v___x_141_ = v___x_102_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_size_99_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object* v_aig_144_, lean_object* v_ref_145_){
_start:
{
lean_object* v_gate_146_; uint8_t v_invert_147_; lean_object* v_decls_148_; lean_object* v_decl_149_; 
v_gate_146_ = lean_ctor_get(v_ref_145_, 0);
v_invert_147_ = lean_ctor_get_uint8(v_ref_145_, sizeof(void*)*1);
v_decls_148_ = lean_ctor_get(v_aig_144_, 0);
v_decl_149_ = lean_array_fget_borrowed(v_decls_148_, v_gate_146_);
if (lean_obj_tag(v_decl_149_) == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_box(v_invert_147_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_box(0);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object* v_aig_153_, lean_object* v_ref_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v_aig_153_, v_ref_154_);
lean_dec_ref(v_ref_154_);
lean_dec_ref(v_aig_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_158_; 
lean_dec(v_a_156_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v_key_159_; lean_object* v_value_160_; lean_object* v_tail_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_key_159_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_key_159_);
v_value_160_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_value_160_);
v_tail_161_ = lean_ctor_get(v_x_157_, 2);
lean_inc(v_tail_161_);
lean_dec_ref(v_x_157_);
v___x_162_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_156_);
v___x_163_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_162_, v_key_159_, v_a_156_);
if (v___x_163_ == 0)
{
lean_dec(v_value_160_);
v_x_157_ = v_tail_161_;
goto _start;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_tail_161_);
lean_dec(v_a_156_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_value_160_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_buckets_168_; lean_object* v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v_fold_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_buckets_168_ = lean_ctor_get(v_m_166_, 1);
v___x_169_ = lean_array_get_size(v_buckets_168_);
v___x_170_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(v_a_167_);
v___x_171_ = 32ULL;
v___x_172_ = lean_uint64_shift_right(v___x_170_, v___x_171_);
v_fold_173_ = lean_uint64_xor(v___x_170_, v___x_172_);
v___x_174_ = 16ULL;
v___x_175_ = lean_uint64_shift_right(v_fold_173_, v___x_174_);
v___x_176_ = lean_uint64_xor(v_fold_173_, v___x_175_);
v___x_177_ = lean_uint64_to_usize(v___x_176_);
v___x_178_ = lean_usize_of_nat(v___x_169_);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_sub(v___x_178_, v___x_179_);
v___x_181_ = lean_usize_land(v___x_177_, v___x_180_);
v___x_182_ = lean_array_uget_borrowed(v_buckets_168_, v___x_181_);
lean_inc(v___x_182_);
v___x_183_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_167_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_184_, v_a_185_);
lean_dec_ref(v_m_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object* v_aig_190_, lean_object* v_input_191_){
_start:
{
lean_object* v_lhs_192_; lean_object* v_rhs_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_276_; 
v_lhs_192_ = lean_ctor_get(v_input_191_, 0);
v_rhs_193_ = lean_ctor_get(v_input_191_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_input_191_);
if (v_isSharedCheck_276_ == 0)
{
v___x_195_ = v_input_191_;
v_isShared_196_ = v_isSharedCheck_276_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_rhs_193_);
lean_inc(v_lhs_192_);
lean_dec(v_input_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_276_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_decls_197_; lean_object* v_cache_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_275_; 
v_decls_197_ = lean_ctor_get(v_aig_190_, 0);
v_cache_198_ = lean_ctor_get(v_aig_190_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_aig_190_);
if (v_isSharedCheck_275_ == 0)
{
v___x_200_ = v_aig_190_;
v_isShared_201_ = v_isSharedCheck_275_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_cache_198_);
lean_inc(v_decls_197_);
lean_dec(v_aig_190_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_275_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_gate_202_; uint8_t v_invert_203_; lean_object* v_gate_204_; uint8_t v_invert_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_decl_214_; 
v_gate_202_ = lean_ctor_get(v_lhs_192_, 0);
lean_inc(v_gate_202_);
v_invert_203_ = lean_ctor_get_uint8(v_lhs_192_, sizeof(void*)*1);
v_gate_204_ = lean_ctor_get(v_rhs_193_, 0);
v_invert_205_ = lean_ctor_get_uint8(v_rhs_193_, sizeof(void*)*1);
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_nat_mul(v_gate_202_, v___x_206_);
v___x_208_ = l_Bool_toNat(v_invert_203_);
v___x_209_ = lean_nat_lor(v___x_207_, v___x_208_);
lean_dec(v___x_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_nat_mul(v_gate_204_, v___x_206_);
v___x_211_ = l_Bool_toNat(v_invert_205_);
v___x_212_ = lean_nat_lor(v___x_210_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_210_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 2);
lean_ctor_set(v___x_195_, 1, v___x_212_);
lean_ctor_set(v___x_195_, 0, v___x_209_);
v_decl_214_ = v___x_195_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_212_);
v_decl_214_ = v_reuseFailAlloc_274_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
lean_inc_ref(v_decl_214_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_cache_198_, v_decl_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_217_; 
lean_inc(v_gate_204_);
lean_inc_ref(v_cache_198_);
lean_inc_ref(v_decls_197_);
if (v_isShared_201_ == 0)
{
v___x_217_ = v___x_200_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_decls_197_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_cache_198_);
v___x_217_ = v_reuseFailAlloc_259_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
uint8_t v___y_219_; uint8_t v___y_224_; lean_object* v_lhsVal_233_; lean_object* v_rhsVal_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_257_; 
v_lhsVal_233_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_217_, v_lhs_192_);
lean_dec_ref(v_lhs_192_);
v_rhsVal_234_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(v___x_217_, v_rhs_193_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_rhs_193_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_rhs_193_, 0);
lean_dec(v_unused_258_);
v___x_236_ = v_rhs_193_;
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_rhs_193_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v_ref_221_; lean_object* v___x_222_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v_ref_221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_221_, 0, v___x_220_);
lean_ctor_set_uint8(v_ref_221_, sizeof(void*)*1, v___y_219_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_217_);
lean_ctor_set(v___x_222_, 1, v_ref_221_);
return v___x_222_;
}
v___jp_223_:
{
if (v___y_224_ == 0)
{
lean_dec(v_gate_202_);
v___y_219_ = v___y_224_;
goto v___jp_218_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_225_, 0, v_gate_202_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v_invert_203_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_217_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_228_, 0, v_gate_204_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v_invert_205_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_217_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
v___jp_230_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0));
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_217_);
lean_ctor_set(v___x_232_, 1, v_ref_231_);
return v___x_232_;
}
v_resetjp_235_:
{
if (lean_obj_tag(v_lhsVal_233_) == 1)
{
lean_object* v_val_238_; uint8_t v___x_239_; 
lean_del_object(v___x_236_);
lean_dec_ref(v_decl_214_);
lean_dec(v_gate_202_);
lean_dec_ref(v_cache_198_);
lean_dec_ref(v_decls_197_);
v_val_238_ = lean_ctor_get(v_lhsVal_233_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v_lhsVal_233_);
v___x_239_ = lean_unbox(v_val_238_);
lean_dec(v_val_238_);
if (v___x_239_ == 0)
{
lean_dec(v_rhsVal_234_);
lean_dec(v_gate_204_);
goto v___jp_230_;
}
else
{
if (lean_obj_tag(v_rhsVal_234_) == 1)
{
lean_object* v_val_240_; uint8_t v___x_241_; 
v_val_240_ = lean_ctor_get(v_rhsVal_234_, 0);
lean_inc(v_val_240_);
lean_dec_ref(v_rhsVal_234_);
v___x_241_ = lean_unbox(v_val_240_);
lean_dec(v_val_240_);
if (v___x_241_ == 0)
{
lean_dec(v_gate_204_);
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
lean_dec_ref(v_decl_214_);
lean_dec(v_gate_204_);
lean_dec_ref(v_cache_198_);
lean_dec_ref(v_decls_197_);
v_val_242_ = lean_ctor_get(v_rhsVal_234_, 0);
lean_inc(v_val_242_);
lean_dec_ref(v_rhsVal_234_);
v___x_243_ = lean_unbox(v_val_242_);
lean_dec(v_val_242_);
if (v___x_243_ == 0)
{
lean_del_object(v___x_236_);
lean_dec(v_gate_202_);
goto v___jp_230_;
}
else
{
lean_object* v___x_245_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_gate_202_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_gate_202_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v_invert_203_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_217_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
}
}
else
{
uint8_t v___x_248_; 
lean_dec(v_rhsVal_234_);
v___x_248_ = lean_nat_dec_eq(v_gate_202_, v_gate_204_);
lean_dec(v_gate_204_);
if (v___x_248_ == 0)
{
lean_object* v_g_249_; lean_object* v_cache_250_; lean_object* v_decls_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec_ref(v___x_217_);
lean_dec(v_gate_202_);
v_g_249_ = lean_array_get_size(v_decls_197_);
lean_inc_ref(v_decl_214_);
v_cache_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_cache_198_, v_decl_214_, v_g_249_);
v_decls_251_ = lean_array_push(v_decls_197_, v_decl_214_);
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
lean_dec_ref(v_decl_214_);
lean_dec_ref(v_cache_198_);
lean_dec_ref(v_decls_197_);
if (v_invert_203_ == 0)
{
if (v_invert_205_ == 0)
{
v___y_224_ = v___x_248_;
goto v___jp_223_;
}
else
{
lean_dec(v_gate_202_);
v___y_219_ = v_invert_203_;
goto v___jp_218_;
}
}
else
{
v___y_224_ = v_invert_205_;
goto v___jp_223_;
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
lean_dec_ref(v_decl_214_);
lean_dec(v_gate_202_);
lean_dec_ref(v_lhs_192_);
v_isSharedCheck_272_ = !lean_is_exclusive(v_rhs_193_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_rhs_193_, 0);
lean_dec(v_unused_273_);
v___x_261_ = v_rhs_193_;
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_rhs_193_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_val_263_; lean_object* v___x_265_; 
v_val_263_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_263_);
lean_dec_ref(v___x_215_);
if (v_isShared_201_ == 0)
{
v___x_265_ = v___x_200_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_decls_197_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_cache_198_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object* v_aig_277_, lean_object* v_input_278_){
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
v___x_289_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_277_, v___x_288_);
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
v___x_293_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(v_aig_277_, v___x_292_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object* v_aig_296_, lean_object* v_input_297_){
_start:
{
lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; lean_object* v_lhs_359_; lean_object* v_rhs_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_404_; 
v_lhs_359_ = lean_ctor_get(v_input_297_, 0);
v_rhs_360_ = lean_ctor_get(v_input_297_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_input_297_);
if (v_isSharedCheck_404_ == 0)
{
v___x_362_ = v_input_297_;
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_rhs_360_);
lean_inc(v_lhs_359_);
lean_dec(v_input_297_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
v___jp_298_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___y_300_);
lean_ctor_set(v___x_302_, 1, v___y_301_);
v___x_303_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_299_, v___x_302_);
return v___x_303_;
}
v___jp_304_:
{
uint8_t v_invert_308_; 
v_invert_308_ = lean_ctor_get_uint8(v___y_306_, sizeof(void*)*1);
if (v_invert_308_ == 0)
{
lean_object* v_gate_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
v_gate_309_ = lean_ctor_get(v___y_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___y_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v___y_306_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_gate_309_);
lean_dec(v___y_306_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; lean_object* v___x_315_; 
v___x_313_ = 1;
if (v_isShared_312_ == 0)
{
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_gate_309_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_313_);
v___y_299_ = v___y_305_;
v___y_300_ = v___y_307_;
v___y_301_ = v___x_315_;
goto v___jp_298_;
}
}
}
else
{
lean_object* v_gate_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_gate_318_ = lean_ctor_get(v___y_306_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___y_306_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___y_306_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_gate_318_);
lean_dec(v___y_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; lean_object* v___x_324_; 
v___x_322_ = 0;
if (v_isShared_321_ == 0)
{
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_gate_318_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_322_);
v___y_299_ = v___y_305_;
v___y_300_ = v___y_307_;
v___y_301_ = v___x_324_;
goto v___jp_298_;
}
}
}
}
v___jp_327_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_res_335_; uint8_t v_invert_336_; 
v___x_333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_333_, 0, v___y_328_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*1, v___y_331_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v_res_335_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_330_, v___x_334_);
v_invert_336_ = lean_ctor_get_uint8(v___y_329_, sizeof(void*)*1);
if (v_invert_336_ == 0)
{
lean_object* v_aig_337_; lean_object* v_ref_338_; lean_object* v_gate_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_aig_337_ = lean_ctor_get(v_res_335_, 0);
lean_inc_ref(v_aig_337_);
v_ref_338_ = lean_ctor_get(v_res_335_, 1);
lean_inc_ref(v_ref_338_);
lean_dec_ref(v_res_335_);
v_gate_339_ = lean_ctor_get(v___y_329_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___y_329_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v___y_329_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_gate_339_);
lean_dec(v___y_329_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint8_t v___x_343_; lean_object* v___x_345_; 
v___x_343_ = 1;
if (v_isShared_342_ == 0)
{
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_gate_339_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*1, v___x_343_);
v___y_305_ = v_aig_337_;
v___y_306_ = v_ref_338_;
v___y_307_ = v___x_345_;
goto v___jp_304_;
}
}
}
else
{
lean_object* v_aig_348_; lean_object* v_ref_349_; lean_object* v_gate_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_aig_348_ = lean_ctor_get(v_res_335_, 0);
lean_inc_ref(v_aig_348_);
v_ref_349_ = lean_ctor_get(v_res_335_, 1);
lean_inc_ref(v_ref_349_);
lean_dec_ref(v_res_335_);
v_gate_350_ = lean_ctor_get(v___y_329_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___y_329_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___y_329_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_gate_350_);
lean_dec(v___y_329_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; lean_object* v___x_356_; 
v___x_354_ = 0;
if (v_isShared_353_ == 0)
{
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_gate_350_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*1, v___x_354_);
v___y_305_ = v_aig_348_;
v___y_306_ = v_ref_349_;
v___y_307_ = v___x_356_;
goto v___jp_304_;
}
}
}
}
v_resetjp_361_:
{
lean_object* v_gate_364_; uint8_t v_invert_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_403_; 
v_gate_364_ = lean_ctor_get(v_lhs_359_, 0);
v_invert_365_ = lean_ctor_get_uint8(v_lhs_359_, sizeof(void*)*1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_lhs_359_);
if (v_isSharedCheck_403_ == 0)
{
v___x_367_ = v_lhs_359_;
v_isShared_368_ = v_isSharedCheck_403_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_gate_364_);
lean_dec(v_lhs_359_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_403_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_gate_369_; uint8_t v_invert_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_402_; 
v_gate_369_ = lean_ctor_get(v_rhs_360_, 0);
v_invert_370_ = lean_ctor_get_uint8(v_rhs_360_, sizeof(void*)*1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_rhs_360_);
if (v_isSharedCheck_402_ == 0)
{
v___x_372_ = v_rhs_360_;
v_isShared_373_ = v_isSharedCheck_402_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_gate_369_);
lean_dec(v_rhs_360_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_402_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; lean_object* v___x_390_; 
lean_inc(v_gate_364_);
if (v_isShared_368_ == 0)
{
v___x_390_ = v___x_367_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_gate_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*1, v_invert_365_);
v___x_390_ = v_reuseFailAlloc_401_;
goto v_reusejp_389_;
}
v___jp_374_:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_296_, v___y_375_);
if (v_invert_365_ == 0)
{
lean_object* v_aig_377_; lean_object* v_ref_378_; uint8_t v___x_379_; lean_object* v___x_381_; 
v_aig_377_ = lean_ctor_get(v_res_376_, 0);
lean_inc_ref(v_aig_377_);
v_ref_378_ = lean_ctor_get(v_res_376_, 1);
lean_inc_ref(v_ref_378_);
lean_dec_ref(v_res_376_);
v___x_379_ = 1;
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_gate_364_);
v___x_381_ = v___x_372_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_gate_364_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_379_);
v___y_328_ = v_gate_369_;
v___y_329_ = v_ref_378_;
v___y_330_ = v_aig_377_;
v___y_331_ = v_invert_370_;
v___y_332_ = v___x_381_;
goto v___jp_327_;
}
}
else
{
lean_object* v_aig_383_; lean_object* v_ref_384_; uint8_t v___x_385_; lean_object* v___x_387_; 
v_aig_383_ = lean_ctor_get(v_res_376_, 0);
lean_inc_ref(v_aig_383_);
v_ref_384_ = lean_ctor_get(v_res_376_, 1);
lean_inc_ref(v_ref_384_);
lean_dec_ref(v_res_376_);
v___x_385_ = 0;
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_gate_364_);
v___x_387_ = v___x_372_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_gate_364_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_385_);
v___y_328_ = v_gate_369_;
v___y_329_ = v_ref_384_;
v___y_330_ = v_aig_383_;
v___y_331_ = v_invert_370_;
v___y_332_ = v___x_387_;
goto v___jp_327_;
}
}
}
v_reusejp_389_:
{
if (v_invert_370_ == 0)
{
uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = 1;
lean_inc(v_gate_369_);
v___x_392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_392_, 0, v_gate_369_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_391_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v___x_392_);
lean_ctor_set(v___x_362_, 0, v___x_390_);
v___x_394_ = v___x_362_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v___y_375_ = v___x_394_;
goto v___jp_374_;
}
}
else
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = 0;
lean_inc(v_gate_369_);
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v_gate_369_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_396_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v___x_397_);
lean_ctor_set(v___x_362_, 0, v___x_390_);
v___x_399_ = v___x_362_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v___y_375_ = v___x_399_;
goto v___jp_374_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* v_aig_405_, lean_object* v_input_406_){
_start:
{
lean_object* v___y_408_; lean_object* v_lhs_448_; lean_object* v_rhs_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_499_; 
v_lhs_448_ = lean_ctor_get(v_input_406_, 0);
v_rhs_449_ = lean_ctor_get(v_input_406_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_input_406_);
if (v_isSharedCheck_499_ == 0)
{
v___x_451_ = v_input_406_;
v_isShared_452_ = v_isSharedCheck_499_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_rhs_449_);
lean_inc(v_lhs_448_);
lean_dec(v_input_406_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_499_;
goto v_resetjp_450_;
}
v___jp_407_:
{
lean_object* v_res_409_; lean_object* v_ref_410_; uint8_t v_invert_411_; 
v_res_409_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_405_, v___y_408_);
v_ref_410_ = lean_ctor_get(v_res_409_, 1);
lean_inc_ref(v_ref_410_);
v_invert_411_ = lean_ctor_get_uint8(v_ref_410_, sizeof(void*)*1);
if (v_invert_411_ == 0)
{
lean_object* v_aig_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_428_; 
v_aig_412_ = lean_ctor_get(v_res_409_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_res_409_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_res_409_, 1);
lean_dec(v_unused_429_);
v___x_414_ = v_res_409_;
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_aig_412_);
lean_dec(v_res_409_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_gate_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
v_gate_416_ = lean_ctor_get(v_ref_410_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_ref_410_);
if (v_isSharedCheck_427_ == 0)
{
v___x_418_ = v_ref_410_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_gate_416_);
lean_dec(v_ref_410_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
uint8_t v___x_420_; lean_object* v___x_422_; 
v___x_420_ = 1;
if (v_isShared_419_ == 0)
{
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_gate_416_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1, v___x_420_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_422_);
v___x_424_ = v___x_414_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_aig_412_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
else
{
lean_object* v_aig_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_446_; 
v_aig_430_ = lean_ctor_get(v_res_409_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_res_409_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_res_409_, 1);
lean_dec(v_unused_447_);
v___x_432_ = v_res_409_;
v_isShared_433_ = v_isSharedCheck_446_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_aig_430_);
lean_dec(v_res_409_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_446_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_gate_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v_gate_434_ = lean_ctor_get(v_ref_410_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_ref_410_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v_ref_410_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_gate_434_);
lean_dec(v_ref_410_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
uint8_t v___x_438_; lean_object* v___x_440_; 
v___x_438_ = 0;
if (v_isShared_437_ == 0)
{
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_gate_434_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*1, v___x_438_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_440_);
v___x_442_ = v___x_432_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_aig_430_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
v_resetjp_450_:
{
lean_object* v___y_454_; uint8_t v_invert_480_; 
v_invert_480_ = lean_ctor_get_uint8(v_lhs_448_, sizeof(void*)*1);
if (v_invert_480_ == 0)
{
lean_object* v_gate_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_gate_481_ = lean_ctor_get(v_lhs_448_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_lhs_448_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v_lhs_448_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_gate_481_);
lean_dec(v_lhs_448_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; lean_object* v___x_487_; 
v___x_485_ = 1;
if (v_isShared_484_ == 0)
{
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_gate_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*1, v___x_485_);
v___y_454_ = v___x_487_;
goto v___jp_453_;
}
}
}
else
{
lean_object* v_gate_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_gate_490_ = lean_ctor_get(v_lhs_448_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_lhs_448_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v_lhs_448_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_gate_490_);
lean_dec(v_lhs_448_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint8_t v___x_494_; lean_object* v___x_496_; 
v___x_494_ = 0;
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
v___y_454_ = v___x_496_;
goto v___jp_453_;
}
}
}
v___jp_453_:
{
uint8_t v_invert_455_; 
v_invert_455_ = lean_ctor_get_uint8(v_rhs_449_, sizeof(void*)*1);
if (v_invert_455_ == 0)
{
lean_object* v_gate_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_467_; 
v_gate_456_ = lean_ctor_get(v_rhs_449_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_rhs_449_);
if (v_isSharedCheck_467_ == 0)
{
v___x_458_ = v_rhs_449_;
v_isShared_459_ = v_isSharedCheck_467_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_gate_456_);
lean_dec(v_rhs_449_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_467_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint8_t v___x_460_; lean_object* v___x_462_; 
v___x_460_ = 1;
if (v_isShared_459_ == 0)
{
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_gate_456_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_460_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_462_);
lean_ctor_set(v___x_451_, 0, v___y_454_);
v___x_464_ = v___x_451_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___y_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v___y_408_ = v___x_464_;
goto v___jp_407_;
}
}
}
}
else
{
lean_object* v_gate_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_479_; 
v_gate_468_ = lean_ctor_get(v_rhs_449_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_rhs_449_);
if (v_isSharedCheck_479_ == 0)
{
v___x_470_ = v_rhs_449_;
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_gate_468_);
lean_dec(v_rhs_449_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; lean_object* v___x_474_; 
v___x_472_ = 0;
if (v_isShared_471_ == 0)
{
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_gate_468_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*1, v___x_472_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_474_);
lean_ctor_set(v___x_451_, 0, v___y_454_);
v___x_476_ = v___x_451_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___y_454_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
v___y_408_ = v___x_476_;
goto v___jp_407_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* v_aig_500_, lean_object* v_input_501_){
_start:
{
lean_object* v_discr_502_; lean_object* v_lhs_503_; lean_object* v_rhs_504_; lean_object* v___x_505_; lean_object* v_res_506_; lean_object* v_aig_507_; lean_object* v_ref_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_561_; 
v_discr_502_ = lean_ctor_get(v_input_501_, 0);
lean_inc_ref(v_discr_502_);
v_lhs_503_ = lean_ctor_get(v_input_501_, 1);
lean_inc_ref(v_lhs_503_);
v_rhs_504_ = lean_ctor_get(v_input_501_, 2);
lean_inc_ref(v_rhs_504_);
lean_dec_ref(v_input_501_);
lean_inc_ref(v_discr_502_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_discr_502_);
lean_ctor_set(v___x_505_, 1, v_lhs_503_);
v_res_506_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_500_, v___x_505_);
v_aig_507_ = lean_ctor_get(v_res_506_, 0);
v_ref_508_ = lean_ctor_get(v_res_506_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_res_506_);
if (v_isSharedCheck_561_ == 0)
{
v___x_510_ = v_res_506_;
v_isShared_511_ = v_isSharedCheck_561_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_ref_508_);
lean_inc(v_aig_507_);
lean_dec(v_res_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_561_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_gate_512_; uint8_t v_invert_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_560_; 
v_gate_512_ = lean_ctor_get(v_discr_502_, 0);
v_invert_513_ = lean_ctor_get_uint8(v_discr_502_, sizeof(void*)*1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_discr_502_);
if (v_isSharedCheck_560_ == 0)
{
v___x_515_ = v_discr_502_;
v_isShared_516_ = v_isSharedCheck_560_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_gate_512_);
lean_dec(v_discr_502_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_560_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_gate_517_; uint8_t v_invert_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_559_; 
v_gate_517_ = lean_ctor_get(v_rhs_504_, 0);
v_invert_518_ = lean_ctor_get_uint8(v_rhs_504_, sizeof(void*)*1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_rhs_504_);
if (v_isSharedCheck_559_ == 0)
{
v___x_520_ = v_rhs_504_;
v_isShared_521_ = v_isSharedCheck_559_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_gate_517_);
lean_dec(v_rhs_504_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_559_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_aig_523_; lean_object* v_ref_524_; 
if (v_invert_513_ == 0)
{
uint8_t v___x_551_; lean_object* v___x_553_; 
v___x_551_ = 1;
if (v_isShared_516_ == 0)
{
v___x_553_ = v___x_515_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_gate_512_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*1, v___x_551_);
v_aig_523_ = v_aig_507_;
v_ref_524_ = v___x_553_;
goto v___jp_522_;
}
}
else
{
uint8_t v___x_555_; lean_object* v___x_557_; 
v___x_555_ = 0;
if (v_isShared_516_ == 0)
{
v___x_557_ = v___x_515_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_gate_512_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v___x_555_);
v_aig_523_ = v_aig_507_;
v_ref_524_ = v___x_557_;
goto v___jp_522_;
}
}
v___jp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_521_ == 0)
{
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_gate_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*1, v_invert_518_);
v___x_526_ = v_reuseFailAlloc_550_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_526_);
lean_ctor_set(v___x_510_, 0, v_ref_524_);
v___x_528_ = v___x_510_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_ref_524_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_549_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v_res_529_; lean_object* v_aig_530_; lean_object* v_ref_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_548_; 
v_res_529_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_523_, v___x_528_);
v_aig_530_ = lean_ctor_get(v_res_529_, 0);
v_ref_531_ = lean_ctor_get(v_res_529_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_res_529_);
if (v_isSharedCheck_548_ == 0)
{
v___x_533_ = v_res_529_;
v_isShared_534_ = v_isSharedCheck_548_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_ref_531_);
lean_inc(v_aig_530_);
lean_dec(v_res_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_548_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_gate_535_; uint8_t v_invert_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
v_gate_535_ = lean_ctor_get(v_ref_508_, 0);
v_invert_536_ = lean_ctor_get_uint8(v_ref_508_, sizeof(void*)*1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_ref_508_);
if (v_isSharedCheck_547_ == 0)
{
v___x_538_ = v_ref_508_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_gate_535_);
lean_dec(v_ref_508_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_lhsRef_541_; 
if (v_isShared_539_ == 0)
{
v_lhsRef_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_gate_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*1, v_invert_536_);
v_lhsRef_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_lhsRef_541_);
v___x_543_ = v___x_533_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_lhsRef_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_ref_531_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_530_, v___x_543_);
return v___x_544_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* v_aig_562_, lean_object* v_input_563_){
_start:
{
lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v_res_593_; lean_object* v_aig_594_; lean_object* v_ref_595_; lean_object* v___y_597_; lean_object* v_lhs_622_; lean_object* v_rhs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_663_; 
lean_inc_ref(v_input_563_);
v_res_593_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_562_, v_input_563_);
v_aig_594_ = lean_ctor_get(v_res_593_, 0);
lean_inc_ref(v_aig_594_);
v_ref_595_ = lean_ctor_get(v_res_593_, 1);
lean_inc_ref(v_ref_595_);
lean_dec_ref(v_res_593_);
v_lhs_622_ = lean_ctor_get(v_input_563_, 0);
v_rhs_623_ = lean_ctor_get(v_input_563_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_input_563_);
if (v_isSharedCheck_663_ == 0)
{
v___x_625_ = v_input_563_;
v_isShared_626_ = v_isSharedCheck_663_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_rhs_623_);
lean_inc(v_lhs_622_);
lean_dec(v_input_563_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_663_;
goto v_resetjp_624_;
}
v___jp_564_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___y_566_);
lean_ctor_set(v___x_568_, 1, v___y_567_);
v___x_569_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_565_, v___x_568_);
return v___x_569_;
}
v___jp_570_:
{
uint8_t v_invert_574_; 
v_invert_574_ = lean_ctor_get_uint8(v___y_572_, sizeof(void*)*1);
if (v_invert_574_ == 0)
{
lean_object* v_gate_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_gate_575_ = lean_ctor_get(v___y_572_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___y_572_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v___y_572_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_gate_575_);
lean_dec(v___y_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___x_579_; lean_object* v___x_581_; 
v___x_579_ = 1;
if (v_isShared_578_ == 0)
{
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_gate_575_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*1, v___x_579_);
v___y_565_ = v___y_571_;
v___y_566_ = v___y_573_;
v___y_567_ = v___x_581_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v_gate_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_gate_584_ = lean_ctor_get(v___y_572_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___y_572_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___y_572_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_gate_584_);
lean_dec(v___y_572_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v___x_588_; lean_object* v___x_590_; 
v___x_588_ = 0;
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
v___y_565_ = v___y_571_;
v___y_566_ = v___y_573_;
v___y_567_ = v___x_590_;
goto v___jp_564_;
}
}
}
}
v___jp_596_:
{
lean_object* v_res_598_; uint8_t v_invert_599_; 
v_res_598_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_594_, v___y_597_);
v_invert_599_ = lean_ctor_get_uint8(v_ref_595_, sizeof(void*)*1);
if (v_invert_599_ == 0)
{
lean_object* v_aig_600_; lean_object* v_ref_601_; lean_object* v_gate_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_aig_600_ = lean_ctor_get(v_res_598_, 0);
lean_inc_ref(v_aig_600_);
v_ref_601_ = lean_ctor_get(v_res_598_, 1);
lean_inc_ref(v_ref_601_);
lean_dec_ref(v_res_598_);
v_gate_602_ = lean_ctor_get(v_ref_595_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_ref_595_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_ref_595_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_gate_602_);
lean_dec(v_ref_595_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; lean_object* v___x_608_; 
v___x_606_ = 1;
if (v_isShared_605_ == 0)
{
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_gate_602_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_606_);
v___y_571_ = v_aig_600_;
v___y_572_ = v_ref_601_;
v___y_573_ = v___x_608_;
goto v___jp_570_;
}
}
}
else
{
lean_object* v_aig_611_; lean_object* v_ref_612_; lean_object* v_gate_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
v_aig_611_ = lean_ctor_get(v_res_598_, 0);
lean_inc_ref(v_aig_611_);
v_ref_612_ = lean_ctor_get(v_res_598_, 1);
lean_inc_ref(v_ref_612_);
lean_dec_ref(v_res_598_);
v_gate_613_ = lean_ctor_get(v_ref_595_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_ref_595_);
if (v_isSharedCheck_621_ == 0)
{
v___x_615_ = v_ref_595_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_gate_613_);
lean_dec(v_ref_595_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; lean_object* v___x_619_; 
v___x_617_ = 0;
if (v_isShared_616_ == 0)
{
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_gate_613_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*1, v___x_617_);
v___y_571_ = v_aig_611_;
v___y_572_ = v_ref_612_;
v___y_573_ = v___x_619_;
goto v___jp_570_;
}
}
}
}
v_resetjp_624_:
{
lean_object* v_gate_627_; uint8_t v_invert_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_662_; 
v_gate_627_ = lean_ctor_get(v_lhs_622_, 0);
v_invert_628_ = lean_ctor_get_uint8(v_lhs_622_, sizeof(void*)*1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_lhs_622_);
if (v_isSharedCheck_662_ == 0)
{
v___x_630_ = v_lhs_622_;
v_isShared_631_ = v_isSharedCheck_662_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_gate_627_);
lean_dec(v_lhs_622_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_662_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_gate_632_; uint8_t v_invert_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_661_; 
v_gate_632_ = lean_ctor_get(v_rhs_623_, 0);
v_invert_633_ = lean_ctor_get_uint8(v_rhs_623_, sizeof(void*)*1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_rhs_623_);
if (v_isSharedCheck_661_ == 0)
{
v___x_635_ = v_rhs_623_;
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_gate_632_);
lean_dec(v_rhs_623_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___y_638_; 
if (v_invert_628_ == 0)
{
uint8_t v___x_653_; lean_object* v___x_655_; 
v___x_653_ = 1;
if (v_isShared_631_ == 0)
{
v___x_655_ = v___x_630_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_gate_627_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_653_);
v___y_638_ = v___x_655_;
goto v___jp_637_;
}
}
else
{
uint8_t v___x_657_; lean_object* v___x_659_; 
v___x_657_ = 0;
if (v_isShared_631_ == 0)
{
v___x_659_ = v___x_630_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_gate_627_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_657_);
v___y_638_ = v___x_659_;
goto v___jp_637_;
}
}
v___jp_637_:
{
if (v_invert_633_ == 0)
{
uint8_t v___x_639_; lean_object* v___x_641_; 
v___x_639_ = 1;
if (v_isShared_636_ == 0)
{
v___x_641_ = v___x_635_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_gate_632_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_639_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_641_);
lean_ctor_set(v___x_625_, 0, v___y_638_);
v___x_643_ = v___x_625_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___y_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_597_ = v___x_643_;
goto v___jp_596_;
}
}
}
else
{
uint8_t v___x_646_; lean_object* v___x_648_; 
v___x_646_ = 0;
if (v_isShared_636_ == 0)
{
v___x_648_ = v___x_635_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_gate_632_);
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
lean_ctor_set(v___x_625_, 0, v___y_638_);
v___x_650_ = v___x_625_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___y_638_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_597_ = v___x_650_;
goto v___jp_596_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* v_aig_664_, lean_object* v_expr_665_, lean_object* v_cache_666_){
_start:
{
switch(lean_obj_tag(v_expr_665_))
{
case 0:
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_667_ = lean_ctor_get(v_expr_665_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v_expr_665_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_a_667_);
lean_ctor_set(v___x_668_, 1, v_cache_666_);
v___x_669_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_664_, v___x_668_);
return v___x_669_;
}
case 1:
{
uint8_t v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_a_670_ = lean_ctor_get_uint8(v_expr_665_, 0);
lean_dec_ref(v_expr_665_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v_a_670_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_aig_664_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_cache_666_);
return v___x_674_;
}
case 2:
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v_result_677_; lean_object* v_ref_678_; uint8_t v_invert_679_; 
v_a_675_ = lean_ctor_get(v_expr_665_, 0);
lean_inc_ref(v_a_675_);
lean_dec_ref(v_expr_665_);
v___x_676_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_664_, v_a_675_, v_cache_666_);
v_result_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_result_677_);
v_ref_678_ = lean_ctor_get(v_result_677_, 1);
lean_inc_ref(v_ref_678_);
v_invert_679_ = lean_ctor_get_uint8(v_ref_678_, sizeof(void*)*1);
if (v_invert_679_ == 0)
{
lean_object* v_cache_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_705_; 
v_cache_680_ = lean_ctor_get(v___x_676_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_676_, 0);
lean_dec(v_unused_706_);
v___x_682_ = v___x_676_;
v_isShared_683_ = v_isSharedCheck_705_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_cache_680_);
lean_dec(v___x_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_705_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_aig_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_703_; 
v_aig_684_ = lean_ctor_get(v_result_677_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_result_677_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_result_677_, 1);
lean_dec(v_unused_704_);
v___x_686_ = v_result_677_;
v_isShared_687_ = v_isSharedCheck_703_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_aig_684_);
lean_dec(v_result_677_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_703_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_gate_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_702_; 
v_gate_688_ = lean_ctor_get(v_ref_678_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_ref_678_);
if (v_isSharedCheck_702_ == 0)
{
v___x_690_ = v_ref_678_;
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_gate_688_);
lean_dec(v_ref_678_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; lean_object* v___x_694_; 
v___x_692_ = 1;
if (v_isShared_691_ == 0)
{
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_gate_688_);
v___x_694_ = v_reuseFailAlloc_701_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_692_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_694_);
v___x_696_ = v___x_686_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_aig_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_696_);
v___x_698_ = v___x_682_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_cache_680_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
else
{
lean_object* v_cache_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_732_; 
v_cache_707_ = lean_ctor_get(v___x_676_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_676_, 0);
lean_dec(v_unused_733_);
v___x_709_ = v___x_676_;
v_isShared_710_ = v_isSharedCheck_732_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_cache_707_);
lean_dec(v___x_676_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_732_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_aig_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_730_; 
v_aig_711_ = lean_ctor_get(v_result_677_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_result_677_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_result_677_, 1);
lean_dec(v_unused_731_);
v___x_713_ = v_result_677_;
v_isShared_714_ = v_isSharedCheck_730_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_aig_711_);
lean_dec(v_result_677_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_730_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_gate_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_gate_715_ = lean_ctor_get(v_ref_678_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_ref_678_);
if (v_isSharedCheck_729_ == 0)
{
v___x_717_ = v_ref_678_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_gate_715_);
lean_dec(v_ref_678_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
uint8_t v___x_719_; lean_object* v___x_721_; 
v___x_719_ = 0;
if (v_isShared_718_ == 0)
{
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_gate_715_);
v___x_721_ = v_reuseFailAlloc_728_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_719_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_721_);
v___x_723_ = v___x_713_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_aig_711_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_723_);
v___x_725_ = v___x_709_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_cache_707_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
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
uint8_t v_a_734_; lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v_result_738_; lean_object* v_cache_739_; lean_object* v_aig_740_; lean_object* v_ref_741_; lean_object* v___x_742_; lean_object* v_result_743_; lean_object* v_cache_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_782_; 
v_a_734_ = lean_ctor_get_uint8(v_expr_665_, sizeof(void*)*2);
v_a_735_ = lean_ctor_get(v_expr_665_, 0);
lean_inc_ref(v_a_735_);
v_a_736_ = lean_ctor_get(v_expr_665_, 1);
lean_inc_ref(v_a_736_);
lean_dec_ref(v_expr_665_);
v___x_737_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_664_, v_a_735_, v_cache_666_);
v_result_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc_ref(v_result_738_);
v_cache_739_ = lean_ctor_get(v___x_737_, 1);
lean_inc_ref(v_cache_739_);
lean_dec_ref(v___x_737_);
v_aig_740_ = lean_ctor_get(v_result_738_, 0);
lean_inc_ref(v_aig_740_);
v_ref_741_ = lean_ctor_get(v_result_738_, 1);
lean_inc_ref(v_ref_741_);
lean_dec_ref(v_result_738_);
v___x_742_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_740_, v_a_736_, v_cache_739_);
v_result_743_ = lean_ctor_get(v___x_742_, 0);
v_cache_744_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_782_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_782_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_cache_744_);
lean_inc(v_result_743_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_782_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_aig_748_; lean_object* v_ref_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_781_; 
v_aig_748_ = lean_ctor_get(v_result_743_, 0);
v_ref_749_ = lean_ctor_get(v_result_743_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_result_743_);
if (v_isSharedCheck_781_ == 0)
{
v___x_751_ = v_result_743_;
v_isShared_752_ = v_isSharedCheck_781_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_ref_749_);
lean_inc(v_aig_748_);
lean_dec(v_result_743_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_781_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_gate_753_; uint8_t v_invert_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_780_; 
v_gate_753_ = lean_ctor_get(v_ref_741_, 0);
v_invert_754_ = lean_ctor_get_uint8(v_ref_741_, sizeof(void*)*1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_ref_741_);
if (v_isSharedCheck_780_ == 0)
{
v___x_756_ = v_ref_741_;
v_isShared_757_ = v_isSharedCheck_780_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_gate_753_);
lean_dec(v_ref_741_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_780_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_lhsRef_759_; 
if (v_isShared_757_ == 0)
{
v_lhsRef_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_gate_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*1, v_invert_754_);
v_lhsRef_759_ = v_reuseFailAlloc_779_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v_input_761_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v_lhsRef_759_);
v_input_761_ = v___x_751_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_lhsRef_759_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_ref_749_);
v_input_761_ = v_reuseFailAlloc_778_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
switch(v_a_734_)
{
case 0:
{
lean_object* v_ret_762_; lean_object* v___x_764_; 
v_ret_762_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_748_, v_input_761_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_ret_762_);
v___x_764_ = v___x_746_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_ret_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_cache_744_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
case 1:
{
lean_object* v_ret_766_; lean_object* v___x_768_; 
v_ret_766_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_748_, v_input_761_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_ret_766_);
v___x_768_ = v___x_746_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_ret_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_cache_744_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
case 2:
{
lean_object* v_ret_770_; lean_object* v___x_772_; 
v_ret_770_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_748_, v_input_761_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_ret_770_);
v___x_772_ = v___x_746_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_ret_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_cache_744_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
default: 
{
lean_object* v_ret_774_; lean_object* v___x_776_; 
v_ret_774_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_748_, v_input_761_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_ret_774_);
v___x_776_ = v___x_746_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_ret_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_cache_744_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
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
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_833_; 
v_a_783_ = lean_ctor_get(v_expr_665_, 0);
v_a_784_ = lean_ctor_get(v_expr_665_, 1);
v_a_785_ = lean_ctor_get(v_expr_665_, 2);
v_isSharedCheck_833_ = !lean_is_exclusive(v_expr_665_);
if (v_isSharedCheck_833_ == 0)
{
v___x_787_ = v_expr_665_;
v_isShared_788_ = v_isSharedCheck_833_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_inc(v_a_784_);
lean_inc(v_a_783_);
lean_dec(v_expr_665_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_833_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_result_790_; lean_object* v_cache_791_; lean_object* v_aig_792_; lean_object* v_ref_793_; lean_object* v___x_794_; lean_object* v_result_795_; lean_object* v_cache_796_; lean_object* v_aig_797_; lean_object* v_ref_798_; lean_object* v___x_799_; lean_object* v_result_800_; lean_object* v_cache_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_832_; 
v___x_789_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_664_, v_a_783_, v_cache_666_);
v_result_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_result_790_);
v_cache_791_ = lean_ctor_get(v___x_789_, 1);
lean_inc_ref(v_cache_791_);
lean_dec_ref(v___x_789_);
v_aig_792_ = lean_ctor_get(v_result_790_, 0);
lean_inc_ref(v_aig_792_);
v_ref_793_ = lean_ctor_get(v_result_790_, 1);
lean_inc_ref(v_ref_793_);
lean_dec_ref(v_result_790_);
v___x_794_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_792_, v_a_784_, v_cache_791_);
v_result_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_result_795_);
v_cache_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc_ref(v_cache_796_);
lean_dec_ref(v___x_794_);
v_aig_797_ = lean_ctor_get(v_result_795_, 0);
lean_inc_ref(v_aig_797_);
v_ref_798_ = lean_ctor_get(v_result_795_, 1);
lean_inc_ref(v_ref_798_);
lean_dec_ref(v_result_795_);
v___x_799_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_797_, v_a_785_, v_cache_796_);
v_result_800_ = lean_ctor_get(v___x_799_, 0);
v_cache_801_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_832_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_832_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_cache_801_);
lean_inc(v_result_800_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_832_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_aig_805_; lean_object* v_ref_806_; lean_object* v_gate_807_; uint8_t v_invert_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_831_; 
v_aig_805_ = lean_ctor_get(v_result_800_, 0);
lean_inc_ref(v_aig_805_);
v_ref_806_ = lean_ctor_get(v_result_800_, 1);
lean_inc_ref(v_ref_806_);
lean_dec_ref(v_result_800_);
v_gate_807_ = lean_ctor_get(v_ref_793_, 0);
v_invert_808_ = lean_ctor_get_uint8(v_ref_793_, sizeof(void*)*1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_ref_793_);
if (v_isSharedCheck_831_ == 0)
{
v___x_810_ = v_ref_793_;
v_isShared_811_ = v_isSharedCheck_831_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_gate_807_);
lean_dec(v_ref_793_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_831_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_gate_812_; uint8_t v_invert_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_830_; 
v_gate_812_ = lean_ctor_get(v_ref_798_, 0);
v_invert_813_ = lean_ctor_get_uint8(v_ref_798_, sizeof(void*)*1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_ref_798_);
if (v_isSharedCheck_830_ == 0)
{
v___x_815_ = v_ref_798_;
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_gate_812_);
lean_dec(v_ref_798_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_discrRef_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_gate_807_);
v_discrRef_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_gate_807_);
v_discrRef_818_ = v_reuseFailAlloc_829_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v_lhsRef_820_; 
lean_ctor_set_uint8(v_discrRef_818_, sizeof(void*)*1, v_invert_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_gate_812_);
v_lhsRef_820_ = v___x_810_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_gate_812_);
v_lhsRef_820_ = v_reuseFailAlloc_828_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v_input_822_; 
lean_ctor_set_uint8(v_lhsRef_820_, sizeof(void*)*1, v_invert_813_);
if (v_isShared_788_ == 0)
{
lean_ctor_set_tag(v___x_787_, 0);
lean_ctor_set(v___x_787_, 2, v_ref_806_);
lean_ctor_set(v___x_787_, 1, v_lhsRef_820_);
lean_ctor_set(v___x_787_, 0, v_discrRef_818_);
v_input_822_ = v___x_787_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_discrRef_818_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_lhsRef_820_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_ref_806_);
v_input_822_ = v_reuseFailAlloc_827_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v_ret_823_; lean_object* v___x_825_; 
v_ret_823_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_805_, v_input_822_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v_ret_823_);
v___x_825_ = v___x_803_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_ret_823_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_cache_801_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_834_, lean_object* v_m_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_835_, v_a_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_838_, lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_838_, v_m_839_, v_a_840_);
lean_dec_ref(v_m_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_842_, lean_object* v_m_843_, lean_object* v_a_844_, lean_object* v_b_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_843_, v_a_844_, v_b_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_851_, lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_855_, lean_object* v_a_856_, lean_object* v_x_857_){
_start:
{
uint8_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_855_, v_a_856_, v_x_857_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_860_, lean_object* v_data_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_863_, lean_object* v_a_864_, lean_object* v_b_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_864_, v_b_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_868_, lean_object* v_i_869_, lean_object* v_source_870_, lean_object* v_target_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_869_, v_source_870_, v_target_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_874_, v_x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v___x_882_ = lean_unsigned_to_nat(16u);
v___x_883_ = lean_mk_array(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_888_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
return v___x_889_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_890_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_unsigned_to_nat(16u);
v___x_893_ = lean_mk_array(v___x_892_, v___x_891_);
return v___x_893_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_result_901_; 
v___x_898_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_899_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_900_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_898_, v_expr_897_, v___x_899_);
v_result_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_result_901_);
lean_dec_ref(v___x_900_);
return v_result_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* v_expr_902_, lean_object* v_h__1_903_, lean_object* v_h__2_904_, lean_object* v_h__3_905_, lean_object* v_h__4_906_, lean_object* v_h__5_907_){
_start:
{
switch(lean_obj_tag(v_expr_902_))
{
case 0:
{
lean_object* v_a_908_; lean_object* v___x_909_; 
lean_dec(v_h__5_907_);
lean_dec(v_h__4_906_);
lean_dec(v_h__3_905_);
lean_dec(v_h__2_904_);
v_a_908_ = lean_ctor_get(v_expr_902_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v_expr_902_);
v___x_909_ = lean_apply_1(v_h__1_903_, v_a_908_);
return v___x_909_;
}
case 1:
{
uint8_t v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v_h__5_907_);
lean_dec(v_h__4_906_);
lean_dec(v_h__3_905_);
lean_dec(v_h__1_903_);
v_a_910_ = lean_ctor_get_uint8(v_expr_902_, 0);
lean_dec_ref(v_expr_902_);
v___x_911_ = lean_box(v_a_910_);
v___x_912_ = lean_apply_1(v_h__2_904_, v___x_911_);
return v___x_912_;
}
case 2:
{
lean_object* v_a_913_; lean_object* v___x_914_; 
lean_dec(v_h__5_907_);
lean_dec(v_h__4_906_);
lean_dec(v_h__2_904_);
lean_dec(v_h__1_903_);
v_a_913_ = lean_ctor_get(v_expr_902_, 0);
lean_inc_ref(v_a_913_);
lean_dec_ref(v_expr_902_);
v___x_914_ = lean_apply_1(v_h__3_905_, v_a_913_);
return v___x_914_;
}
case 3:
{
uint8_t v_a_915_; lean_object* v_a_916_; lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_h__4_906_);
lean_dec(v_h__3_905_);
lean_dec(v_h__2_904_);
lean_dec(v_h__1_903_);
v_a_915_ = lean_ctor_get_uint8(v_expr_902_, sizeof(void*)*2);
v_a_916_ = lean_ctor_get(v_expr_902_, 0);
lean_inc_ref(v_a_916_);
v_a_917_ = lean_ctor_get(v_expr_902_, 1);
lean_inc_ref(v_a_917_);
lean_dec_ref(v_expr_902_);
v___x_918_ = lean_box(v_a_915_);
v___x_919_ = lean_apply_3(v_h__5_907_, v___x_918_, v_a_916_, v_a_917_);
return v___x_919_;
}
default: 
{
lean_object* v_a_920_; lean_object* v_a_921_; lean_object* v_a_922_; lean_object* v___x_923_; 
lean_dec(v_h__5_907_);
lean_dec(v_h__3_905_);
lean_dec(v_h__2_904_);
lean_dec(v_h__1_903_);
v_a_920_ = lean_ctor_get(v_expr_902_, 0);
lean_inc_ref(v_a_920_);
v_a_921_ = lean_ctor_get(v_expr_902_, 1);
lean_inc_ref(v_a_921_);
v_a_922_ = lean_ctor_get(v_expr_902_, 2);
lean_inc_ref(v_a_922_);
lean_dec_ref(v_expr_902_);
v___x_923_ = lean_apply_3(v_h__4_906_, v_a_920_, v_a_921_, v_a_922_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* v_motive_924_, lean_object* v_expr_925_, lean_object* v_h__1_926_, lean_object* v_h__2_927_, lean_object* v_h__3_928_, lean_object* v_h__4_929_, lean_object* v_h__5_930_){
_start:
{
switch(lean_obj_tag(v_expr_925_))
{
case 0:
{
lean_object* v_a_931_; lean_object* v___x_932_; 
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
v_a_931_ = lean_ctor_get(v_expr_925_, 0);
lean_inc(v_a_931_);
lean_dec_ref(v_expr_925_);
v___x_932_ = lean_apply_1(v_h__1_926_, v_a_931_);
return v___x_932_;
}
case 1:
{
uint8_t v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__1_926_);
v_a_933_ = lean_ctor_get_uint8(v_expr_925_, 0);
lean_dec_ref(v_expr_925_);
v___x_934_ = lean_box(v_a_933_);
v___x_935_ = lean_apply_1(v_h__2_927_, v___x_934_);
return v___x_935_;
}
case 2:
{
lean_object* v_a_936_; lean_object* v___x_937_; 
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_936_ = lean_ctor_get(v_expr_925_, 0);
lean_inc_ref(v_a_936_);
lean_dec_ref(v_expr_925_);
v___x_937_ = lean_apply_1(v_h__3_928_, v_a_936_);
return v___x_937_;
}
case 3:
{
uint8_t v_a_938_; lean_object* v_a_939_; lean_object* v_a_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_938_ = lean_ctor_get_uint8(v_expr_925_, sizeof(void*)*2);
v_a_939_ = lean_ctor_get(v_expr_925_, 0);
lean_inc_ref(v_a_939_);
v_a_940_ = lean_ctor_get(v_expr_925_, 1);
lean_inc_ref(v_a_940_);
lean_dec_ref(v_expr_925_);
v___x_941_ = lean_box(v_a_938_);
v___x_942_ = lean_apply_3(v_h__5_930_, v___x_941_, v_a_939_, v_a_940_);
return v___x_942_;
}
default: 
{
lean_object* v_a_943_; lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_946_; 
lean_dec(v_h__5_930_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_943_ = lean_ctor_get(v_expr_925_, 0);
lean_inc_ref(v_a_943_);
v_a_944_ = lean_ctor_get(v_expr_925_, 1);
lean_inc_ref(v_a_944_);
v_a_945_ = lean_ctor_get(v_expr_925_, 2);
lean_inc_ref(v_a_945_);
lean_dec_ref(v_expr_925_);
v___x_946_ = lean_apply_3(v_h__4_929_, v_a_943_, v_a_944_, v_a_945_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* v_x_947_, lean_object* v_h__1_948_){
_start:
{
lean_object* v_result_949_; lean_object* v_cache_950_; lean_object* v_aig_951_; lean_object* v_ref_952_; lean_object* v___x_953_; 
v_result_949_ = lean_ctor_get(v_x_947_, 0);
lean_inc_ref(v_result_949_);
v_cache_950_ = lean_ctor_get(v_x_947_, 1);
lean_inc_ref(v_cache_950_);
lean_dec_ref(v_x_947_);
v_aig_951_ = lean_ctor_get(v_result_949_, 0);
lean_inc_ref(v_aig_951_);
v_ref_952_ = lean_ctor_get(v_result_949_, 1);
lean_inc_ref(v_ref_952_);
lean_dec_ref(v_result_949_);
v___x_953_ = lean_apply_4(v_h__1_948_, v_aig_951_, v_ref_952_, lean_box(0), v_cache_950_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* v_aig_954_, lean_object* v_motive_955_, lean_object* v_x_956_, lean_object* v_h__1_957_){
_start:
{
lean_object* v_result_958_; lean_object* v_cache_959_; lean_object* v_aig_960_; lean_object* v_ref_961_; lean_object* v___x_962_; 
v_result_958_ = lean_ctor_get(v_x_956_, 0);
lean_inc_ref(v_result_958_);
v_cache_959_ = lean_ctor_get(v_x_956_, 1);
lean_inc_ref(v_cache_959_);
lean_dec_ref(v_x_956_);
v_aig_960_ = lean_ctor_get(v_result_958_, 0);
lean_inc_ref(v_aig_960_);
v_ref_961_ = lean_ctor_get(v_result_958_, 1);
lean_inc_ref(v_ref_961_);
lean_dec_ref(v_result_958_);
v___x_962_ = lean_apply_4(v_h__1_957_, v_aig_960_, v_ref_961_, lean_box(0), v_cache_959_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* v_aig_963_, lean_object* v_motive_964_, lean_object* v_x_965_, lean_object* v_h__1_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_963_, v_motive_964_, v_x_965_, v_h__1_966_);
lean_dec_ref(v_aig_963_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t v_g_968_, lean_object* v_h__1_969_, lean_object* v_h__2_970_, lean_object* v_h__3_971_, lean_object* v_h__4_972_){
_start:
{
switch(v_g_968_)
{
case 0:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_h__4_972_);
lean_dec(v_h__3_971_);
lean_dec(v_h__2_970_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_apply_1(v_h__1_969_, v___x_973_);
return v___x_974_;
}
case 1:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_h__4_972_);
lean_dec(v_h__3_971_);
lean_dec(v_h__1_969_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_apply_1(v_h__2_970_, v___x_975_);
return v___x_976_;
}
case 2:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_h__4_972_);
lean_dec(v_h__2_970_);
lean_dec(v_h__1_969_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_apply_1(v_h__3_971_, v___x_977_);
return v___x_978_;
}
default: 
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v_h__3_971_);
lean_dec(v_h__2_970_);
lean_dec(v_h__1_969_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_apply_1(v_h__4_972_, v___x_979_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* v_g_981_, lean_object* v_h__1_982_, lean_object* v_h__2_983_, lean_object* v_h__3_984_, lean_object* v_h__4_985_){
_start:
{
uint8_t v_g_46__boxed_986_; lean_object* v_res_987_; 
v_g_46__boxed_986_ = lean_unbox(v_g_981_);
v_res_987_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_46__boxed_986_, v_h__1_982_, v_h__2_983_, v_h__3_984_, v_h__4_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* v_motive_988_, uint8_t v_g_989_, lean_object* v_h__1_990_, lean_object* v_h__2_991_, lean_object* v_h__3_992_, lean_object* v_h__4_993_){
_start:
{
switch(v_g_989_)
{
case 0:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_h__4_993_);
lean_dec(v_h__3_992_);
lean_dec(v_h__2_991_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_apply_1(v_h__1_990_, v___x_994_);
return v___x_995_;
}
case 1:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_h__4_993_);
lean_dec(v_h__3_992_);
lean_dec(v_h__1_990_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_apply_1(v_h__2_991_, v___x_996_);
return v___x_997_;
}
case 2:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_h__4_993_);
lean_dec(v_h__2_991_);
lean_dec(v_h__1_990_);
v___x_998_ = lean_box(0);
v___x_999_ = lean_apply_1(v_h__3_992_, v___x_998_);
return v___x_999_;
}
default: 
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__3_992_);
lean_dec(v_h__2_991_);
lean_dec(v_h__1_990_);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_apply_1(v_h__4_993_, v___x_1000_);
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* v_motive_1002_, lean_object* v_g_1003_, lean_object* v_h__1_1004_, lean_object* v_h__2_1005_, lean_object* v_h__3_1006_, lean_object* v_h__4_1007_){
_start:
{
uint8_t v_g_65__boxed_1008_; lean_object* v_res_1009_; 
v_g_65__boxed_1008_ = lean_unbox(v_g_1003_);
v_res_1009_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_1002_, v_g_65__boxed_1008_, v_h__1_1004_, v_h__2_1005_, v_h__3_1006_, v_h__4_1007_);
return v_res_1009_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
