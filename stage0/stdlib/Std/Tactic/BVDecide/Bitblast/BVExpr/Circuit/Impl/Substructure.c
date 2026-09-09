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
lean_dec_ref_known(v_x_157_, 3);
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
lean_dec_ref_known(v_lhsVal_233_, 1);
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
lean_dec_ref_known(v_rhsVal_234_, 1);
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
lean_dec_ref_known(v_rhsVal_234_, 1);
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
if (v_invert_205_ == 0)
{
if (v_invert_203_ == 0)
{
v___y_224_ = v___x_248_;
goto v___jp_223_;
}
else
{
lean_dec(v_gate_202_);
v___y_219_ = v_invert_205_;
goto v___jp_218_;
}
}
else
{
v___y_224_ = v_invert_203_;
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
lean_dec_ref_known(v___x_215_, 1);
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
lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v_lhs_304_; lean_object* v_rhs_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_418_; 
v_lhs_304_ = lean_ctor_get(v_input_297_, 0);
v_rhs_305_ = lean_ctor_get(v_input_297_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_input_297_);
if (v_isSharedCheck_418_ == 0)
{
v___x_307_ = v_input_297_;
v_isShared_308_ = v_isSharedCheck_418_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_rhs_305_);
lean_inc(v_lhs_304_);
lean_dec(v_input_297_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_418_;
goto v_resetjp_306_;
}
v___jp_298_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___y_299_);
lean_ctor_set(v___x_302_, 1, v___y_301_);
v___x_303_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_300_, v___x_302_);
return v___x_303_;
}
v_resetjp_306_:
{
lean_object* v_gate_309_; uint8_t v_invert_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_417_; 
v_gate_309_ = lean_ctor_get(v_lhs_304_, 0);
v_invert_310_ = lean_ctor_get_uint8(v_lhs_304_, sizeof(void*)*1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_lhs_304_);
if (v_isSharedCheck_417_ == 0)
{
v___x_312_ = v_lhs_304_;
v_isShared_313_ = v_isSharedCheck_417_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_gate_309_);
lean_dec(v_lhs_304_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_417_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; uint8_t v___x_315_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; lean_object* v___y_368_; lean_object* v___y_382_; lean_object* v___y_407_; 
v___x_314_ = 0;
v___x_315_ = 1;
if (v_invert_310_ == 0)
{
lean_object* v___x_415_; 
lean_inc(v_gate_309_);
v___x_415_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_415_, 0, v_gate_309_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*1, v___x_314_);
v___y_407_ = v___x_415_;
goto v___jp_406_;
}
else
{
lean_object* v___x_416_; 
lean_inc(v_gate_309_);
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v_gate_309_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_315_);
v___y_407_ = v___x_416_;
goto v___jp_406_;
}
v___jp_316_:
{
uint8_t v_invert_320_; 
v_invert_320_ = lean_ctor_get_uint8(v___y_317_, sizeof(void*)*1);
if (v_invert_320_ == 0)
{
lean_object* v_gate_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_gate_321_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___y_317_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_gate_321_);
lean_dec(v___y_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_gate_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_315_);
v___y_299_ = v___y_319_;
v___y_300_ = v___y_318_;
v___y_301_ = v___x_326_;
goto v___jp_298_;
}
}
}
else
{
lean_object* v_gate_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_gate_329_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___y_317_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_gate_329_);
lean_dec(v___y_317_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_gate_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_314_);
v___y_299_ = v___y_319_;
v___y_300_ = v___y_318_;
v___y_301_ = v___x_334_;
goto v___jp_298_;
}
}
}
}
v___jp_337_:
{
lean_object* v_res_341_; uint8_t v_invert_342_; 
v_res_341_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_339_, v___y_340_);
v_invert_342_ = lean_ctor_get_uint8(v___y_338_, sizeof(void*)*1);
if (v_invert_342_ == 0)
{
lean_object* v_aig_343_; lean_object* v_ref_344_; lean_object* v_gate_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_aig_343_ = lean_ctor_get(v_res_341_, 0);
lean_inc_ref(v_aig_343_);
v_ref_344_ = lean_ctor_get(v_res_341_, 1);
lean_inc_ref(v_ref_344_);
lean_dec_ref(v_res_341_);
v_gate_345_ = lean_ctor_get(v___y_338_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___y_338_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___y_338_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_gate_345_);
lean_dec(v___y_338_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_gate_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1, v___x_315_);
v___y_317_ = v_ref_344_;
v___y_318_ = v_aig_343_;
v___y_319_ = v___x_350_;
goto v___jp_316_;
}
}
}
else
{
lean_object* v_aig_353_; lean_object* v_ref_354_; lean_object* v_gate_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_aig_353_ = lean_ctor_get(v_res_341_, 0);
lean_inc_ref(v_aig_353_);
v_ref_354_ = lean_ctor_get(v_res_341_, 1);
lean_inc_ref(v_ref_354_);
lean_dec_ref(v_res_341_);
v_gate_355_ = lean_ctor_get(v___y_338_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___y_338_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___y_338_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_gate_355_);
lean_dec(v___y_338_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_gate_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*1, v___x_314_);
v___y_317_ = v_ref_354_;
v___y_318_ = v_aig_353_;
v___y_319_ = v___x_360_;
goto v___jp_316_;
}
}
}
}
v___jp_363_:
{
if (v___y_367_ == 0)
{
lean_object* v___x_370_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___y_364_);
v___x_370_ = v___x_312_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___y_364_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v___x_314_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_370_);
lean_ctor_set(v___x_307_, 0, v___y_368_);
v___x_372_ = v___x_307_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___y_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v___y_338_ = v___y_365_;
v___y_339_ = v___y_366_;
v___y_340_ = v___x_372_;
goto v___jp_337_;
}
}
}
else
{
lean_object* v___x_376_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___y_364_);
v___x_376_ = v___x_312_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___y_364_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_315_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_376_);
lean_ctor_set(v___x_307_, 0, v___y_368_);
v___x_378_ = v___x_307_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___y_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
v___y_338_ = v___y_365_;
v___y_339_ = v___y_366_;
v___y_340_ = v___x_378_;
goto v___jp_337_;
}
}
}
}
v___jp_381_:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_296_, v___y_382_);
if (v_invert_310_ == 0)
{
lean_object* v_aig_384_; lean_object* v_ref_385_; lean_object* v_gate_386_; uint8_t v_invert_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_aig_384_ = lean_ctor_get(v_res_383_, 0);
lean_inc_ref(v_aig_384_);
v_ref_385_ = lean_ctor_get(v_res_383_, 1);
lean_inc_ref(v_ref_385_);
lean_dec_ref(v_res_383_);
v_gate_386_ = lean_ctor_get(v_rhs_305_, 0);
v_invert_387_ = lean_ctor_get_uint8(v_rhs_305_, sizeof(void*)*1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_rhs_305_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v_rhs_305_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_gate_386_);
lean_dec(v_rhs_305_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_gate_309_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_gate_309_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_315_);
v___y_364_ = v_gate_386_;
v___y_365_ = v_ref_385_;
v___y_366_ = v_aig_384_;
v___y_367_ = v_invert_387_;
v___y_368_ = v___x_392_;
goto v___jp_363_;
}
}
}
else
{
lean_object* v_aig_395_; lean_object* v_ref_396_; lean_object* v_gate_397_; uint8_t v_invert_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_aig_395_ = lean_ctor_get(v_res_383_, 0);
lean_inc_ref(v_aig_395_);
v_ref_396_ = lean_ctor_get(v_res_383_, 1);
lean_inc_ref(v_ref_396_);
lean_dec_ref(v_res_383_);
v_gate_397_ = lean_ctor_get(v_rhs_305_, 0);
v_invert_398_ = lean_ctor_get_uint8(v_rhs_305_, sizeof(void*)*1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_rhs_305_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v_rhs_305_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_gate_397_);
lean_dec(v_rhs_305_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_gate_309_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_gate_309_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_314_);
v___y_364_ = v_gate_397_;
v___y_365_ = v_ref_396_;
v___y_366_ = v_aig_395_;
v___y_367_ = v_invert_398_;
v___y_368_ = v___x_403_;
goto v___jp_363_;
}
}
}
}
v___jp_406_:
{
uint8_t v_invert_408_; 
v_invert_408_ = lean_ctor_get_uint8(v_rhs_305_, sizeof(void*)*1);
if (v_invert_408_ == 0)
{
lean_object* v_gate_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_gate_409_ = lean_ctor_get(v_rhs_305_, 0);
lean_inc(v_gate_409_);
v___x_410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_410_, 0, v_gate_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_315_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___y_407_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___y_382_ = v___x_411_;
goto v___jp_381_;
}
else
{
lean_object* v_gate_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_gate_412_ = lean_ctor_get(v_rhs_305_, 0);
lean_inc(v_gate_412_);
v___x_413_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_413_, 0, v_gate_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_314_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_407_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___y_382_ = v___x_414_;
goto v___jp_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* v_aig_419_, lean_object* v_input_420_){
_start:
{
lean_object* v___y_422_; lean_object* v_lhs_462_; lean_object* v_rhs_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_507_; 
v_lhs_462_ = lean_ctor_get(v_input_420_, 0);
v_rhs_463_ = lean_ctor_get(v_input_420_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_input_420_);
if (v_isSharedCheck_507_ == 0)
{
v___x_465_ = v_input_420_;
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_rhs_463_);
lean_inc(v_lhs_462_);
lean_dec(v_input_420_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
v___jp_421_:
{
lean_object* v_res_423_; lean_object* v_ref_424_; uint8_t v_invert_425_; 
v_res_423_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_419_, v___y_422_);
v_ref_424_ = lean_ctor_get(v_res_423_, 1);
lean_inc_ref(v_ref_424_);
v_invert_425_ = lean_ctor_get_uint8(v_ref_424_, sizeof(void*)*1);
if (v_invert_425_ == 0)
{
lean_object* v_aig_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_442_; 
v_aig_426_ = lean_ctor_get(v_res_423_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_res_423_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v_res_423_, 1);
lean_dec(v_unused_443_);
v___x_428_ = v_res_423_;
v_isShared_429_ = v_isSharedCheck_442_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_aig_426_);
lean_dec(v_res_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_442_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_gate_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_441_; 
v_gate_430_ = lean_ctor_get(v_ref_424_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_ref_424_);
if (v_isSharedCheck_441_ == 0)
{
v___x_432_ = v_ref_424_;
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_gate_430_);
lean_dec(v_ref_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; lean_object* v___x_436_; 
v___x_434_ = 1;
if (v_isShared_433_ == 0)
{
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_gate_430_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_434_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_436_);
v___x_438_ = v___x_428_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_aig_426_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
else
{
lean_object* v_aig_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_460_; 
v_aig_444_ = lean_ctor_get(v_res_423_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_res_423_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_res_423_, 1);
lean_dec(v_unused_461_);
v___x_446_ = v_res_423_;
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_aig_444_);
lean_dec(v_res_423_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_460_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_gate_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_459_; 
v_gate_448_ = lean_ctor_get(v_ref_424_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_ref_424_);
if (v_isSharedCheck_459_ == 0)
{
v___x_450_ = v_ref_424_;
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_gate_448_);
lean_dec(v_ref_424_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v___x_452_; lean_object* v___x_454_; 
v___x_452_ = 0;
if (v_isShared_451_ == 0)
{
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_gate_448_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___x_452_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_454_);
v___x_456_ = v___x_446_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_aig_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
v_resetjp_464_:
{
lean_object* v_gate_467_; uint8_t v_invert_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_506_; 
v_gate_467_ = lean_ctor_get(v_lhs_462_, 0);
v_invert_468_ = lean_ctor_get_uint8(v_lhs_462_, sizeof(void*)*1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_lhs_462_);
if (v_isSharedCheck_506_ == 0)
{
v___x_470_ = v_lhs_462_;
v_isShared_471_ = v_isSharedCheck_506_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_gate_467_);
lean_dec(v_lhs_462_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_506_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; lean_object* v___y_474_; 
v___x_472_ = 1;
if (v_invert_468_ == 0)
{
lean_object* v___x_500_; 
if (v_isShared_471_ == 0)
{
v___x_500_ = v___x_470_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_gate_467_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_472_);
v___y_474_ = v___x_500_;
goto v___jp_473_;
}
}
else
{
uint8_t v___x_502_; lean_object* v___x_504_; 
v___x_502_ = 0;
if (v_isShared_471_ == 0)
{
v___x_504_ = v___x_470_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_gate_467_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_502_);
v___y_474_ = v___x_504_;
goto v___jp_473_;
}
}
v___jp_473_:
{
uint8_t v_invert_475_; 
v_invert_475_ = lean_ctor_get_uint8(v_rhs_463_, sizeof(void*)*1);
if (v_invert_475_ == 0)
{
lean_object* v_gate_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v_gate_476_ = lean_ctor_get(v_rhs_463_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_rhs_463_);
if (v_isSharedCheck_486_ == 0)
{
v___x_478_ = v_rhs_463_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_gate_476_);
lean_dec(v_rhs_463_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_gate_476_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
lean_ctor_set_uint8(v___x_481_, sizeof(void*)*1, v___x_472_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_481_);
lean_ctor_set(v___x_465_, 0, v___y_474_);
v___x_483_ = v___x_465_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___y_474_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
v___y_422_ = v___x_483_;
goto v___jp_421_;
}
}
}
}
else
{
lean_object* v_gate_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_498_; 
v_gate_487_ = lean_ctor_get(v_rhs_463_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_rhs_463_);
if (v_isSharedCheck_498_ == 0)
{
v___x_489_ = v_rhs_463_;
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_gate_487_);
lean_dec(v_rhs_463_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; lean_object* v___x_493_; 
v___x_491_ = 0;
if (v_isShared_490_ == 0)
{
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_gate_487_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*1, v___x_491_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_493_);
lean_ctor_set(v___x_465_, 0, v___y_474_);
v___x_495_ = v___x_465_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___y_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
v___y_422_ = v___x_495_;
goto v___jp_421_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* v_aig_508_, lean_object* v_input_509_){
_start:
{
lean_object* v_discr_510_; lean_object* v_lhs_511_; lean_object* v_rhs_512_; lean_object* v___x_513_; lean_object* v_res_514_; lean_object* v_aig_515_; lean_object* v_ref_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_569_; 
v_discr_510_ = lean_ctor_get(v_input_509_, 0);
lean_inc_ref_n(v_discr_510_, 2);
v_lhs_511_ = lean_ctor_get(v_input_509_, 1);
lean_inc_ref(v_lhs_511_);
v_rhs_512_ = lean_ctor_get(v_input_509_, 2);
lean_inc_ref(v_rhs_512_);
lean_dec_ref(v_input_509_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_discr_510_);
lean_ctor_set(v___x_513_, 1, v_lhs_511_);
v_res_514_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_508_, v___x_513_);
v_aig_515_ = lean_ctor_get(v_res_514_, 0);
v_ref_516_ = lean_ctor_get(v_res_514_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_res_514_);
if (v_isSharedCheck_569_ == 0)
{
v___x_518_ = v_res_514_;
v_isShared_519_ = v_isSharedCheck_569_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_ref_516_);
lean_inc(v_aig_515_);
lean_dec(v_res_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_569_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_gate_520_; uint8_t v_invert_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_568_; 
v_gate_520_ = lean_ctor_get(v_discr_510_, 0);
v_invert_521_ = lean_ctor_get_uint8(v_discr_510_, sizeof(void*)*1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_discr_510_);
if (v_isSharedCheck_568_ == 0)
{
v___x_523_ = v_discr_510_;
v_isShared_524_ = v_isSharedCheck_568_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_gate_520_);
lean_dec(v_discr_510_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_568_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_gate_525_; uint8_t v_invert_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_567_; 
v_gate_525_ = lean_ctor_get(v_rhs_512_, 0);
v_invert_526_ = lean_ctor_get_uint8(v_rhs_512_, sizeof(void*)*1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_rhs_512_);
if (v_isSharedCheck_567_ == 0)
{
v___x_528_ = v_rhs_512_;
v_isShared_529_ = v_isSharedCheck_567_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_gate_525_);
lean_dec(v_rhs_512_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_567_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_aig_531_; lean_object* v_ref_532_; 
if (v_invert_521_ == 0)
{
uint8_t v___x_559_; lean_object* v___x_561_; 
v___x_559_ = 1;
if (v_isShared_524_ == 0)
{
v___x_561_ = v___x_523_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_gate_520_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_559_);
v_aig_531_ = v_aig_515_;
v_ref_532_ = v___x_561_;
goto v___jp_530_;
}
}
else
{
uint8_t v___x_563_; lean_object* v___x_565_; 
v___x_563_ = 0;
if (v_isShared_524_ == 0)
{
v___x_565_ = v___x_523_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_gate_520_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_563_);
v_aig_531_ = v_aig_515_;
v_ref_532_ = v___x_565_;
goto v___jp_530_;
}
}
v___jp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_529_ == 0)
{
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_gate_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*1, v_invert_526_);
v___x_534_ = v_reuseFailAlloc_558_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_534_);
lean_ctor_set(v___x_518_, 0, v_ref_532_);
v___x_536_ = v___x_518_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_ref_532_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_557_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v_res_537_; lean_object* v_aig_538_; lean_object* v_ref_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_556_; 
v_res_537_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_531_, v___x_536_);
v_aig_538_ = lean_ctor_get(v_res_537_, 0);
v_ref_539_ = lean_ctor_get(v_res_537_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_res_537_);
if (v_isSharedCheck_556_ == 0)
{
v___x_541_ = v_res_537_;
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_ref_539_);
lean_inc(v_aig_538_);
lean_dec(v_res_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_gate_543_; uint8_t v_invert_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
v_gate_543_ = lean_ctor_get(v_ref_516_, 0);
v_invert_544_ = lean_ctor_get_uint8(v_ref_516_, sizeof(void*)*1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_ref_516_);
if (v_isSharedCheck_555_ == 0)
{
v___x_546_ = v_ref_516_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_gate_543_);
lean_dec(v_ref_516_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_lhsRef_549_; 
if (v_isShared_547_ == 0)
{
v_lhsRef_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_gate_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*1, v_invert_544_);
v_lhsRef_549_ = v_reuseFailAlloc_554_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_lhsRef_549_);
v___x_551_ = v___x_541_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_lhsRef_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_ref_539_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_538_, v___x_551_);
return v___x_552_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* v_aig_570_, lean_object* v_input_571_){
_start:
{
lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v_res_601_; lean_object* v_aig_602_; lean_object* v_ref_603_; lean_object* v___y_605_; lean_object* v_lhs_630_; lean_object* v_rhs_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_670_; 
lean_inc_ref(v_input_571_);
v_res_601_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_570_, v_input_571_);
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
lean_ctor_set(v___x_576_, 0, v___y_573_);
lean_ctor_set(v___x_576_, 1, v___y_575_);
v___x_577_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v___y_574_, v___x_576_);
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
v___y_573_ = v___y_581_;
v___y_574_ = v___y_579_;
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
v___y_573_ = v___y_581_;
v___y_574_ = v___y_579_;
v___y_575_ = v___x_598_;
goto v___jp_572_;
}
}
}
}
v___jp_604_:
{
lean_object* v_res_606_; uint8_t v_invert_607_; 
v_res_606_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_602_, v___y_605_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* v_aig_671_, lean_object* v_expr_672_, lean_object* v_cache_673_){
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
v___x_683_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_671_, v_a_682_, v_cache_673_);
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
v___x_744_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_671_, v_a_742_, v_cache_673_);
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
v___x_749_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_747_, v_a_743_, v_cache_746_);
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
v_ret_769_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_755_, v_input_768_);
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
v_ret_773_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_755_, v_input_768_);
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
v_ret_777_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_755_, v_input_768_);
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
v_ret_781_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_755_, v_input_768_);
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
v___x_796_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_671_, v_a_790_, v_cache_673_);
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
v___x_801_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_799_, v_a_791_, v_cache_798_);
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
v___x_806_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_804_, v_a_792_, v_cache_803_);
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
v_ret_830_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_812_, v_input_829_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_842_, v_a_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_845_, lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_845_, v_m_846_, v_a_847_);
lean_dec_ref(v_m_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_849_, lean_object* v_m_850_, lean_object* v_a_851_, lean_object* v_b_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_850_, v_a_851_, v_b_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_854_, lean_object* v_a_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_858_, lean_object* v_a_859_, lean_object* v_x_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_862_, lean_object* v_a_863_, lean_object* v_x_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_862_, v_a_863_, v_x_864_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_867_, lean_object* v_data_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_870_, lean_object* v_a_871_, lean_object* v_b_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_871_, v_b_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_875_, lean_object* v_i_876_, lean_object* v_source_877_, lean_object* v_target_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_876_, v_source_877_, v_target_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_881_, v_x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_unsigned_to_nat(16u);
v___x_890_ = lean_mk_array(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_891_);
return v___x_893_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_895_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_897_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_unsigned_to_nat(16u);
v___x_900_ = lean_mk_array(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_result_908_; 
v___x_905_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_906_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_907_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_905_, v_expr_904_, v___x_906_);
v_result_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_result_908_);
lean_dec_ref(v___x_907_);
return v_result_908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* v_expr_909_, lean_object* v_h__1_910_, lean_object* v_h__2_911_, lean_object* v_h__3_912_, lean_object* v_h__4_913_, lean_object* v_h__5_914_){
_start:
{
switch(lean_obj_tag(v_expr_909_))
{
case 0:
{
lean_object* v_a_915_; lean_object* v___x_916_; 
lean_dec(v_h__5_914_);
lean_dec(v_h__4_913_);
lean_dec(v_h__3_912_);
lean_dec(v_h__2_911_);
v_a_915_ = lean_ctor_get(v_expr_909_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v_expr_909_, 1);
v___x_916_ = lean_apply_1(v_h__1_910_, v_a_915_);
return v___x_916_;
}
case 1:
{
uint8_t v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_h__5_914_);
lean_dec(v_h__4_913_);
lean_dec(v_h__3_912_);
lean_dec(v_h__1_910_);
v_a_917_ = lean_ctor_get_uint8(v_expr_909_, 0);
lean_dec_ref_known(v_expr_909_, 0);
v___x_918_ = lean_box(v_a_917_);
v___x_919_ = lean_apply_1(v_h__2_911_, v___x_918_);
return v___x_919_;
}
case 2:
{
lean_object* v_a_920_; lean_object* v___x_921_; 
lean_dec(v_h__5_914_);
lean_dec(v_h__4_913_);
lean_dec(v_h__2_911_);
lean_dec(v_h__1_910_);
v_a_920_ = lean_ctor_get(v_expr_909_, 0);
lean_inc_ref(v_a_920_);
lean_dec_ref_known(v_expr_909_, 1);
v___x_921_ = lean_apply_1(v_h__3_912_, v_a_920_);
return v___x_921_;
}
case 3:
{
uint8_t v_a_922_; lean_object* v_a_923_; lean_object* v_a_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_h__4_913_);
lean_dec(v_h__3_912_);
lean_dec(v_h__2_911_);
lean_dec(v_h__1_910_);
v_a_922_ = lean_ctor_get_uint8(v_expr_909_, sizeof(void*)*2);
v_a_923_ = lean_ctor_get(v_expr_909_, 0);
lean_inc_ref(v_a_923_);
v_a_924_ = lean_ctor_get(v_expr_909_, 1);
lean_inc_ref(v_a_924_);
lean_dec_ref_known(v_expr_909_, 2);
v___x_925_ = lean_box(v_a_922_);
v___x_926_ = lean_apply_3(v_h__5_914_, v___x_925_, v_a_923_, v_a_924_);
return v___x_926_;
}
default: 
{
lean_object* v_a_927_; lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v___x_930_; 
lean_dec(v_h__5_914_);
lean_dec(v_h__3_912_);
lean_dec(v_h__2_911_);
lean_dec(v_h__1_910_);
v_a_927_ = lean_ctor_get(v_expr_909_, 0);
lean_inc_ref(v_a_927_);
v_a_928_ = lean_ctor_get(v_expr_909_, 1);
lean_inc_ref(v_a_928_);
v_a_929_ = lean_ctor_get(v_expr_909_, 2);
lean_inc_ref(v_a_929_);
lean_dec_ref_known(v_expr_909_, 3);
v___x_930_ = lean_apply_3(v_h__4_913_, v_a_927_, v_a_928_, v_a_929_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* v_motive_931_, lean_object* v_expr_932_, lean_object* v_h__1_933_, lean_object* v_h__2_934_, lean_object* v_h__3_935_, lean_object* v_h__4_936_, lean_object* v_h__5_937_){
_start:
{
switch(lean_obj_tag(v_expr_932_))
{
case 0:
{
lean_object* v_a_938_; lean_object* v___x_939_; 
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
v_a_938_ = lean_ctor_get(v_expr_932_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_expr_932_, 1);
v___x_939_ = lean_apply_1(v_h__1_933_, v_a_938_);
return v___x_939_;
}
case 1:
{
uint8_t v_a_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__1_933_);
v_a_940_ = lean_ctor_get_uint8(v_expr_932_, 0);
lean_dec_ref_known(v_expr_932_, 0);
v___x_941_ = lean_box(v_a_940_);
v___x_942_ = lean_apply_1(v_h__2_934_, v___x_941_);
return v___x_942_;
}
case 2:
{
lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_a_943_ = lean_ctor_get(v_expr_932_, 0);
lean_inc_ref(v_a_943_);
lean_dec_ref_known(v_expr_932_, 1);
v___x_944_ = lean_apply_1(v_h__3_935_, v_a_943_);
return v___x_944_;
}
case 3:
{
uint8_t v_a_945_; lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_a_945_ = lean_ctor_get_uint8(v_expr_932_, sizeof(void*)*2);
v_a_946_ = lean_ctor_get(v_expr_932_, 0);
lean_inc_ref(v_a_946_);
v_a_947_ = lean_ctor_get(v_expr_932_, 1);
lean_inc_ref(v_a_947_);
lean_dec_ref_known(v_expr_932_, 2);
v___x_948_ = lean_box(v_a_945_);
v___x_949_ = lean_apply_3(v_h__5_937_, v___x_948_, v_a_946_, v_a_947_);
return v___x_949_;
}
default: 
{
lean_object* v_a_950_; lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v___x_953_; 
lean_dec(v_h__5_937_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_a_950_ = lean_ctor_get(v_expr_932_, 0);
lean_inc_ref(v_a_950_);
v_a_951_ = lean_ctor_get(v_expr_932_, 1);
lean_inc_ref(v_a_951_);
v_a_952_ = lean_ctor_get(v_expr_932_, 2);
lean_inc_ref(v_a_952_);
lean_dec_ref_known(v_expr_932_, 3);
v___x_953_ = lean_apply_3(v_h__4_936_, v_a_950_, v_a_951_, v_a_952_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* v_x_954_, lean_object* v_h__1_955_){
_start:
{
lean_object* v_result_956_; lean_object* v_cache_957_; lean_object* v_aig_958_; lean_object* v_ref_959_; lean_object* v___x_960_; 
v_result_956_ = lean_ctor_get(v_x_954_, 0);
lean_inc_ref(v_result_956_);
v_cache_957_ = lean_ctor_get(v_x_954_, 1);
lean_inc_ref(v_cache_957_);
lean_dec_ref(v_x_954_);
v_aig_958_ = lean_ctor_get(v_result_956_, 0);
lean_inc_ref(v_aig_958_);
v_ref_959_ = lean_ctor_get(v_result_956_, 1);
lean_inc_ref(v_ref_959_);
lean_dec_ref(v_result_956_);
v___x_960_ = lean_apply_4(v_h__1_955_, v_aig_958_, v_ref_959_, lean_box(0), v_cache_957_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* v_aig_961_, lean_object* v_motive_962_, lean_object* v_x_963_, lean_object* v_h__1_964_){
_start:
{
lean_object* v_result_965_; lean_object* v_cache_966_; lean_object* v_aig_967_; lean_object* v_ref_968_; lean_object* v___x_969_; 
v_result_965_ = lean_ctor_get(v_x_963_, 0);
lean_inc_ref(v_result_965_);
v_cache_966_ = lean_ctor_get(v_x_963_, 1);
lean_inc_ref(v_cache_966_);
lean_dec_ref(v_x_963_);
v_aig_967_ = lean_ctor_get(v_result_965_, 0);
lean_inc_ref(v_aig_967_);
v_ref_968_ = lean_ctor_get(v_result_965_, 1);
lean_inc_ref(v_ref_968_);
lean_dec_ref(v_result_965_);
v___x_969_ = lean_apply_4(v_h__1_964_, v_aig_967_, v_ref_968_, lean_box(0), v_cache_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* v_aig_970_, lean_object* v_motive_971_, lean_object* v_x_972_, lean_object* v_h__1_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_970_, v_motive_971_, v_x_972_, v_h__1_973_);
lean_dec_ref(v_aig_970_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t v_g_975_, lean_object* v_h__1_976_, lean_object* v_h__2_977_, lean_object* v_h__3_978_, lean_object* v_h__4_979_){
_start:
{
switch(v_g_975_)
{
case 0:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v_h__4_979_);
lean_dec(v_h__3_978_);
lean_dec(v_h__2_977_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_apply_1(v_h__1_976_, v___x_980_);
return v___x_981_;
}
case 1:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_h__4_979_);
lean_dec(v_h__3_978_);
lean_dec(v_h__1_976_);
v___x_982_ = lean_box(0);
v___x_983_ = lean_apply_1(v_h__2_977_, v___x_982_);
return v___x_983_;
}
case 2:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec(v_h__4_979_);
lean_dec(v_h__2_977_);
lean_dec(v_h__1_976_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_apply_1(v_h__3_978_, v___x_984_);
return v___x_985_;
}
default: 
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_h__3_978_);
lean_dec(v_h__2_977_);
lean_dec(v_h__1_976_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_apply_1(v_h__4_979_, v___x_986_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* v_g_988_, lean_object* v_h__1_989_, lean_object* v_h__2_990_, lean_object* v_h__3_991_, lean_object* v_h__4_992_){
_start:
{
uint8_t v_g_42__boxed_993_; lean_object* v_res_994_; 
v_g_42__boxed_993_ = lean_unbox(v_g_988_);
v_res_994_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_42__boxed_993_, v_h__1_989_, v_h__2_990_, v_h__3_991_, v_h__4_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* v_motive_995_, uint8_t v_g_996_, lean_object* v_h__1_997_, lean_object* v_h__2_998_, lean_object* v_h__3_999_, lean_object* v_h__4_1000_){
_start:
{
switch(v_g_996_)
{
case 0:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_h__4_1000_);
lean_dec(v_h__3_999_);
lean_dec(v_h__2_998_);
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_apply_1(v_h__1_997_, v___x_1001_);
return v___x_1002_;
}
case 1:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__4_1000_);
lean_dec(v_h__3_999_);
lean_dec(v_h__1_997_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_apply_1(v_h__2_998_, v___x_1003_);
return v___x_1004_;
}
case 2:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__4_1000_);
lean_dec(v_h__2_998_);
lean_dec(v_h__1_997_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_apply_1(v_h__3_999_, v___x_1005_);
return v___x_1006_;
}
default: 
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__3_999_);
lean_dec(v_h__2_998_);
lean_dec(v_h__1_997_);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_apply_1(v_h__4_1000_, v___x_1007_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* v_motive_1009_, lean_object* v_g_1010_, lean_object* v_h__1_1011_, lean_object* v_h__2_1012_, lean_object* v_h__3_1013_, lean_object* v_h__4_1014_){
_start:
{
uint8_t v_g_61__boxed_1015_; lean_object* v_res_1016_; 
v_g_61__boxed_1015_ = lean_unbox(v_g_1010_);
v_res_1016_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_1009_, v_g_61__boxed_1015_, v_h__1_1011_, v_h__2_1012_, v_h__3_1013_, v_h__4_1014_);
return v_res_1016_;
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
