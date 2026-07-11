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
uint8_t lean_bool_xor(uint8_t, uint8_t);
lean_object* lean_bool_to_nat(uint8_t);
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
v___x_208_ = lean_bool_to_nat(v_invert_203_);
v___x_209_ = lean_nat_lor(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_nat_mul(v_gate_204_, v___x_206_);
v___x_211_ = lean_bool_to_nat(v_invert_205_);
v___x_212_ = lean_nat_lor(v___x_210_, v___x_211_);
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
lean_object* v_lhs_298_; lean_object* v_rhs_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_373_; 
v_lhs_298_ = lean_ctor_get(v_input_297_, 0);
v_rhs_299_ = lean_ctor_get(v_input_297_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_input_297_);
if (v_isSharedCheck_373_ == 0)
{
v___x_301_ = v_input_297_;
v_isShared_302_ = v_isSharedCheck_373_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_rhs_299_);
lean_inc(v_lhs_298_);
lean_dec(v_input_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_373_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_gate_303_; uint8_t v_invert_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_372_; 
v_gate_303_ = lean_ctor_get(v_lhs_298_, 0);
v_invert_304_ = lean_ctor_get_uint8(v_lhs_298_, sizeof(void*)*1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_lhs_298_);
if (v_isSharedCheck_372_ == 0)
{
v___x_306_ = v_lhs_298_;
v_isShared_307_ = v_isSharedCheck_372_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_gate_303_);
lean_dec(v_lhs_298_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_372_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_gate_308_; uint8_t v_invert_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_371_; 
v_gate_308_ = lean_ctor_get(v_rhs_299_, 0);
v_invert_309_ = lean_ctor_get_uint8(v_rhs_299_, sizeof(void*)*1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_rhs_299_);
if (v_isSharedCheck_371_ == 0)
{
v___x_311_ = v_rhs_299_;
v_isShared_312_ = v_isSharedCheck_371_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_gate_308_);
lean_dec(v_rhs_299_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_371_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; uint8_t v___x_314_; uint8_t v___x_315_; lean_object* v___x_317_; 
v___x_313_ = 0;
v___x_314_ = 1;
v___x_315_ = lean_bool_xor(v___x_313_, v_invert_304_);
lean_inc(v_gate_303_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_gate_303_);
v___x_317_ = v___x_311_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_gate_303_);
v___x_317_ = v_reuseFailAlloc_370_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
uint8_t v___x_318_; lean_object* v___x_320_; 
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*1, v___x_315_);
v___x_318_ = lean_bool_xor(v___x_314_, v_invert_309_);
lean_inc(v_gate_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_gate_308_);
v___x_320_ = v___x_306_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_gate_308_);
v___x_320_ = v_reuseFailAlloc_369_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_318_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_320_);
lean_ctor_set(v___x_301_, 0, v___x_317_);
v___x_322_ = v___x_301_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_368_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v_res_323_; lean_object* v_aig_324_; lean_object* v_ref_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_367_; 
v_res_323_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_296_, v___x_322_);
v_aig_324_ = lean_ctor_get(v_res_323_, 0);
v_ref_325_ = lean_ctor_get(v_res_323_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_res_323_);
if (v_isSharedCheck_367_ == 0)
{
v___x_327_ = v_res_323_;
v_isShared_328_ = v_isSharedCheck_367_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_ref_325_);
lean_inc(v_aig_324_);
lean_dec(v_res_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_367_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_329_ = lean_bool_xor(v___x_314_, v_invert_304_);
v___x_330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_330_, 0, v_gate_303_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*1, v___x_329_);
v___x_331_ = lean_bool_xor(v___x_313_, v_invert_309_);
v___x_332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_332_, 0, v_gate_308_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_331_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_332_);
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_334_ = v___x_327_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_366_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v_res_335_; lean_object* v_ref_336_; lean_object* v_aig_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_365_; 
v_res_335_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_324_, v___x_334_);
v_ref_336_ = lean_ctor_get(v_res_335_, 1);
v_aig_337_ = lean_ctor_get(v_res_335_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_res_335_);
if (v_isSharedCheck_365_ == 0)
{
v___x_339_ = v_res_335_;
v_isShared_340_ = v_isSharedCheck_365_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_ref_336_);
lean_inc(v_aig_337_);
lean_dec(v_res_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_365_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_gate_341_; uint8_t v_invert_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_364_; 
v_gate_341_ = lean_ctor_get(v_ref_325_, 0);
v_invert_342_ = lean_ctor_get_uint8(v_ref_325_, sizeof(void*)*1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_ref_325_);
if (v_isSharedCheck_364_ == 0)
{
v___x_344_ = v_ref_325_;
v_isShared_345_ = v_isSharedCheck_364_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_gate_341_);
lean_dec(v_ref_325_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_364_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_gate_346_; uint8_t v_invert_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_363_; 
v_gate_346_ = lean_ctor_get(v_ref_336_, 0);
v_invert_347_ = lean_ctor_get_uint8(v_ref_336_, sizeof(void*)*1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_ref_336_);
if (v_isSharedCheck_363_ == 0)
{
v___x_349_ = v_ref_336_;
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_gate_346_);
lean_dec(v_ref_336_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
uint8_t v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_bool_xor(v___x_314_, v_invert_342_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_gate_341_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_gate_341_);
v___x_353_ = v_reuseFailAlloc_362_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
uint8_t v___x_354_; lean_object* v___x_356_; 
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*1, v___x_351_);
v___x_354_ = lean_bool_xor(v___x_314_, v_invert_347_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v_gate_346_);
v___x_356_ = v___x_344_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_gate_346_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*1, v___x_354_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_356_);
lean_ctor_set(v___x_339_, 0, v___x_353_);
v___x_358_ = v___x_339_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_337_, v___x_358_);
return v___x_359_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* v_aig_374_, lean_object* v_input_375_){
_start:
{
lean_object* v_lhs_376_; lean_object* v_rhs_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_425_; 
v_lhs_376_ = lean_ctor_get(v_input_375_, 0);
v_rhs_377_ = lean_ctor_get(v_input_375_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_input_375_);
if (v_isSharedCheck_425_ == 0)
{
v___x_379_ = v_input_375_;
v_isShared_380_ = v_isSharedCheck_425_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_rhs_377_);
lean_inc(v_lhs_376_);
lean_dec(v_input_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_425_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_gate_381_; uint8_t v_invert_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_424_; 
v_gate_381_ = lean_ctor_get(v_lhs_376_, 0);
v_invert_382_ = lean_ctor_get_uint8(v_lhs_376_, sizeof(void*)*1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_lhs_376_);
if (v_isSharedCheck_424_ == 0)
{
v___x_384_ = v_lhs_376_;
v_isShared_385_ = v_isSharedCheck_424_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_gate_381_);
lean_dec(v_lhs_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_424_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_gate_386_; uint8_t v_invert_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_423_; 
v_gate_386_ = lean_ctor_get(v_rhs_377_, 0);
v_invert_387_ = lean_ctor_get_uint8(v_rhs_377_, sizeof(void*)*1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_rhs_377_);
if (v_isSharedCheck_423_ == 0)
{
v___x_389_ = v_rhs_377_;
v_isShared_390_ = v_isSharedCheck_423_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_gate_386_);
lean_dec(v_rhs_377_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_423_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; uint8_t v___x_392_; lean_object* v___x_394_; 
v___x_391_ = 1;
v___x_392_ = lean_bool_xor(v___x_391_, v_invert_382_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_gate_381_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_gate_381_);
v___x_394_ = v_reuseFailAlloc_422_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
uint8_t v___x_395_; lean_object* v___x_397_; 
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_392_);
v___x_395_ = lean_bool_xor(v___x_391_, v_invert_387_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_gate_386_);
v___x_397_ = v___x_384_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_gate_386_);
v___x_397_ = v_reuseFailAlloc_421_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_395_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_397_);
lean_ctor_set(v___x_379_, 0, v___x_394_);
v___x_399_ = v___x_379_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_420_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v_res_400_; lean_object* v_ref_401_; lean_object* v_aig_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_419_; 
v_res_400_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_374_, v___x_399_);
v_ref_401_ = lean_ctor_get(v_res_400_, 1);
v_aig_402_ = lean_ctor_get(v_res_400_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_res_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_404_ = v_res_400_;
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_ref_401_);
lean_inc(v_aig_402_);
lean_dec(v_res_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_gate_406_; uint8_t v_invert_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
v_gate_406_ = lean_ctor_get(v_ref_401_, 0);
v_invert_407_ = lean_ctor_get_uint8(v_ref_401_, sizeof(void*)*1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_ref_401_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v_ref_401_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_gate_406_);
lean_dec(v_ref_401_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
uint8_t v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_bool_xor(v___x_391_, v_invert_407_);
if (v_isShared_410_ == 0)
{
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_gate_406_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_411_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_413_);
v___x_415_ = v___x_404_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_aig_402_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* v_aig_426_, lean_object* v_input_427_){
_start:
{
lean_object* v_discr_428_; lean_object* v_lhs_429_; lean_object* v_rhs_430_; lean_object* v___x_431_; lean_object* v_res_432_; lean_object* v_aig_433_; lean_object* v_ref_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_481_; 
v_discr_428_ = lean_ctor_get(v_input_427_, 0);
lean_inc_ref_n(v_discr_428_, 2);
v_lhs_429_ = lean_ctor_get(v_input_427_, 1);
lean_inc_ref(v_lhs_429_);
v_rhs_430_ = lean_ctor_get(v_input_427_, 2);
lean_inc_ref(v_rhs_430_);
lean_dec_ref(v_input_427_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_discr_428_);
lean_ctor_set(v___x_431_, 1, v_lhs_429_);
v_res_432_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_426_, v___x_431_);
v_aig_433_ = lean_ctor_get(v_res_432_, 0);
v_ref_434_ = lean_ctor_get(v_res_432_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_res_432_);
if (v_isSharedCheck_481_ == 0)
{
v___x_436_ = v_res_432_;
v_isShared_437_ = v_isSharedCheck_481_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_ref_434_);
lean_inc(v_aig_433_);
lean_dec(v_res_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_481_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_gate_438_; uint8_t v_invert_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_480_; 
v_gate_438_ = lean_ctor_get(v_discr_428_, 0);
v_invert_439_ = lean_ctor_get_uint8(v_discr_428_, sizeof(void*)*1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_discr_428_);
if (v_isSharedCheck_480_ == 0)
{
v___x_441_ = v_discr_428_;
v_isShared_442_ = v_isSharedCheck_480_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_gate_438_);
lean_dec(v_discr_428_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_480_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_gate_443_; uint8_t v_invert_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_479_; 
v_gate_443_ = lean_ctor_get(v_rhs_430_, 0);
v_invert_444_ = lean_ctor_get_uint8(v_rhs_430_, sizeof(void*)*1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_rhs_430_);
if (v_isSharedCheck_479_ == 0)
{
v___x_446_ = v_rhs_430_;
v_isShared_447_ = v_isSharedCheck_479_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_gate_443_);
lean_dec(v_rhs_430_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_479_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; uint8_t v___x_449_; lean_object* v_notDiscr_451_; 
v___x_448_ = 1;
v___x_449_ = lean_bool_xor(v___x_448_, v_invert_439_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_gate_438_);
v_notDiscr_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_gate_438_);
v_notDiscr_451_ = v_reuseFailAlloc_478_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
lean_ctor_set_uint8(v_notDiscr_451_, sizeof(void*)*1, v___x_449_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v_gate_443_);
v___x_453_ = v___x_441_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_gate_443_);
v___x_453_ = v_reuseFailAlloc_477_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v_invert_444_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_453_);
lean_ctor_set(v___x_436_, 0, v_notDiscr_451_);
v___x_455_ = v___x_436_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_notDiscr_451_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_476_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v_res_456_; lean_object* v_aig_457_; lean_object* v_ref_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_475_; 
v_res_456_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_433_, v___x_455_);
v_aig_457_ = lean_ctor_get(v_res_456_, 0);
v_ref_458_ = lean_ctor_get(v_res_456_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_res_456_);
if (v_isSharedCheck_475_ == 0)
{
v___x_460_ = v_res_456_;
v_isShared_461_ = v_isSharedCheck_475_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_ref_458_);
lean_inc(v_aig_457_);
lean_dec(v_res_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_475_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_gate_462_; uint8_t v_invert_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_474_; 
v_gate_462_ = lean_ctor_get(v_ref_434_, 0);
v_invert_463_ = lean_ctor_get_uint8(v_ref_434_, sizeof(void*)*1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_ref_434_);
if (v_isSharedCheck_474_ == 0)
{
v___x_465_ = v_ref_434_;
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_gate_462_);
lean_dec(v_ref_434_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_lhsRef_468_; 
if (v_isShared_466_ == 0)
{
v_lhsRef_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_gate_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*1, v_invert_463_);
v_lhsRef_468_ = v_reuseFailAlloc_473_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_lhsRef_468_);
v___x_470_ = v___x_460_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_lhsRef_468_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_ref_458_);
v___x_470_ = v_reuseFailAlloc_472_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_457_, v___x_470_);
return v___x_471_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* v_aig_482_, lean_object* v_input_483_){
_start:
{
lean_object* v_res_484_; lean_object* v_lhs_485_; lean_object* v_rhs_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_input_483_);
v_res_484_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_482_, v_input_483_);
v_lhs_485_ = lean_ctor_get(v_input_483_, 0);
v_rhs_486_ = lean_ctor_get(v_input_483_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_input_483_);
if (v_isSharedCheck_547_ == 0)
{
v___x_488_ = v_input_483_;
v_isShared_489_ = v_isSharedCheck_547_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_rhs_486_);
lean_inc(v_lhs_485_);
lean_dec(v_input_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_547_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_aig_490_; lean_object* v_ref_491_; lean_object* v_gate_492_; uint8_t v_invert_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_546_; 
v_aig_490_ = lean_ctor_get(v_res_484_, 0);
lean_inc_ref(v_aig_490_);
v_ref_491_ = lean_ctor_get(v_res_484_, 1);
lean_inc_ref(v_ref_491_);
lean_dec_ref(v_res_484_);
v_gate_492_ = lean_ctor_get(v_lhs_485_, 0);
v_invert_493_ = lean_ctor_get_uint8(v_lhs_485_, sizeof(void*)*1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_lhs_485_);
if (v_isSharedCheck_546_ == 0)
{
v___x_495_ = v_lhs_485_;
v_isShared_496_ = v_isSharedCheck_546_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_gate_492_);
lean_dec(v_lhs_485_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_546_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_gate_497_; uint8_t v_invert_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_545_; 
v_gate_497_ = lean_ctor_get(v_rhs_486_, 0);
v_invert_498_ = lean_ctor_get_uint8(v_rhs_486_, sizeof(void*)*1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_rhs_486_);
if (v_isSharedCheck_545_ == 0)
{
v___x_500_ = v_rhs_486_;
v_isShared_501_ = v_isSharedCheck_545_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_gate_497_);
lean_dec(v_rhs_486_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_545_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___x_505_; 
v___x_502_ = 1;
v___x_503_ = lean_bool_xor(v___x_502_, v_invert_493_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_gate_492_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_gate_492_);
v___x_505_ = v_reuseFailAlloc_544_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
uint8_t v___x_506_; lean_object* v___x_508_; 
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*1, v___x_503_);
v___x_506_ = lean_bool_xor(v___x_502_, v_invert_498_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_gate_497_);
v___x_508_ = v___x_495_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_gate_497_);
v___x_508_ = v_reuseFailAlloc_543_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*1, v___x_506_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_508_);
lean_ctor_set(v___x_488_, 0, v___x_505_);
v___x_510_ = v___x_488_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_542_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v_res_511_; lean_object* v_ref_512_; lean_object* v_aig_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_541_; 
v_res_511_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_490_, v___x_510_);
v_ref_512_ = lean_ctor_get(v_res_511_, 1);
v_aig_513_ = lean_ctor_get(v_res_511_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_res_511_);
if (v_isSharedCheck_541_ == 0)
{
v___x_515_ = v_res_511_;
v_isShared_516_ = v_isSharedCheck_541_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_ref_512_);
lean_inc(v_aig_513_);
lean_dec(v_res_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_541_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_gate_517_; uint8_t v_invert_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_540_; 
v_gate_517_ = lean_ctor_get(v_ref_491_, 0);
v_invert_518_ = lean_ctor_get_uint8(v_ref_491_, sizeof(void*)*1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_ref_491_);
if (v_isSharedCheck_540_ == 0)
{
v___x_520_ = v_ref_491_;
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_gate_517_);
lean_dec(v_ref_491_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_gate_522_; uint8_t v_invert_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_539_; 
v_gate_522_ = lean_ctor_get(v_ref_512_, 0);
v_invert_523_ = lean_ctor_get_uint8(v_ref_512_, sizeof(void*)*1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_ref_512_);
if (v_isSharedCheck_539_ == 0)
{
v___x_525_ = v_ref_512_;
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_gate_522_);
lean_dec(v_ref_512_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
uint8_t v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_bool_xor(v___x_502_, v_invert_518_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v_gate_517_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_gate_517_);
v___x_529_ = v_reuseFailAlloc_538_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
uint8_t v___x_530_; lean_object* v___x_532_; 
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_527_);
v___x_530_ = lean_bool_xor(v___x_502_, v_invert_523_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v_gate_522_);
v___x_532_ = v___x_520_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_gate_522_);
v___x_532_ = v_reuseFailAlloc_537_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_530_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_532_);
lean_ctor_set(v___x_515_, 0, v___x_529_);
v___x_534_ = v___x_515_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_513_, v___x_534_);
return v___x_535_;
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
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* v_aig_548_, lean_object* v_expr_549_, lean_object* v_cache_550_){
_start:
{
switch(lean_obj_tag(v_expr_549_))
{
case 0:
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_551_ = lean_ctor_get(v_expr_549_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_expr_549_, 1);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_a_551_);
lean_ctor_set(v___x_552_, 1, v_cache_550_);
v___x_553_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_548_, v___x_552_);
return v___x_553_;
}
case 1:
{
uint8_t v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_a_554_ = lean_ctor_get_uint8(v_expr_549_, 0);
lean_dec_ref_known(v_expr_549_, 0);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v_a_554_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_aig_548_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_cache_550_);
return v___x_558_;
}
case 2:
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v_result_561_; lean_object* v_ref_562_; lean_object* v_cache_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_590_; 
v_a_559_ = lean_ctor_get(v_expr_549_, 0);
lean_inc_ref(v_a_559_);
lean_dec_ref_known(v_expr_549_, 1);
v___x_560_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_548_, v_a_559_, v_cache_550_);
v_result_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_result_561_);
v_ref_562_ = lean_ctor_get(v_result_561_, 1);
lean_inc_ref(v_ref_562_);
v_cache_563_ = lean_ctor_get(v___x_560_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_560_, 0);
lean_dec(v_unused_591_);
v___x_565_ = v___x_560_;
v_isShared_566_ = v_isSharedCheck_590_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_cache_563_);
lean_dec(v___x_560_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_590_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_aig_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_588_; 
v_aig_567_ = lean_ctor_get(v_result_561_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_result_561_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_result_561_, 1);
lean_dec(v_unused_589_);
v___x_569_ = v_result_561_;
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_aig_567_);
lean_dec(v_result_561_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_588_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_gate_571_; uint8_t v_invert_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_587_; 
v_gate_571_ = lean_ctor_get(v_ref_562_, 0);
v_invert_572_ = lean_ctor_get_uint8(v_ref_562_, sizeof(void*)*1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_ref_562_);
if (v_isSharedCheck_587_ == 0)
{
v___x_574_ = v_ref_562_;
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_gate_571_);
lean_dec(v_ref_562_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
uint8_t v___x_576_; uint8_t v___x_577_; lean_object* v___x_579_; 
v___x_576_ = 1;
v___x_577_ = lean_bool_xor(v___x_576_, v_invert_572_);
if (v_isShared_575_ == 0)
{
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_gate_571_);
v___x_579_ = v_reuseFailAlloc_586_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v_ret_581_; 
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*1, v___x_577_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_579_);
v_ret_581_ = v___x_569_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_aig_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_579_);
v_ret_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_ret_581_);
v___x_583_ = v___x_565_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_ret_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_cache_563_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
case 3:
{
uint8_t v_a_592_; lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v_result_596_; lean_object* v_cache_597_; lean_object* v_aig_598_; lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v_result_601_; lean_object* v_cache_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_640_; 
v_a_592_ = lean_ctor_get_uint8(v_expr_549_, sizeof(void*)*2);
v_a_593_ = lean_ctor_get(v_expr_549_, 0);
lean_inc_ref(v_a_593_);
v_a_594_ = lean_ctor_get(v_expr_549_, 1);
lean_inc_ref(v_a_594_);
lean_dec_ref_known(v_expr_549_, 2);
v___x_595_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_548_, v_a_593_, v_cache_550_);
v_result_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc_ref(v_result_596_);
v_cache_597_ = lean_ctor_get(v___x_595_, 1);
lean_inc_ref(v_cache_597_);
lean_dec_ref(v___x_595_);
v_aig_598_ = lean_ctor_get(v_result_596_, 0);
lean_inc_ref(v_aig_598_);
v_ref_599_ = lean_ctor_get(v_result_596_, 1);
lean_inc_ref(v_ref_599_);
lean_dec_ref(v_result_596_);
v___x_600_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_598_, v_a_594_, v_cache_597_);
v_result_601_ = lean_ctor_get(v___x_600_, 0);
v_cache_602_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_640_ == 0)
{
v___x_604_ = v___x_600_;
v_isShared_605_ = v_isSharedCheck_640_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_cache_602_);
lean_inc(v_result_601_);
lean_dec(v___x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_640_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_aig_606_; lean_object* v_ref_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_639_; 
v_aig_606_ = lean_ctor_get(v_result_601_, 0);
v_ref_607_ = lean_ctor_get(v_result_601_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_result_601_);
if (v_isSharedCheck_639_ == 0)
{
v___x_609_ = v_result_601_;
v_isShared_610_ = v_isSharedCheck_639_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_ref_607_);
lean_inc(v_aig_606_);
lean_dec(v_result_601_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_639_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_gate_611_; uint8_t v_invert_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_638_; 
v_gate_611_ = lean_ctor_get(v_ref_599_, 0);
v_invert_612_ = lean_ctor_get_uint8(v_ref_599_, sizeof(void*)*1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_ref_599_);
if (v_isSharedCheck_638_ == 0)
{
v___x_614_ = v_ref_599_;
v_isShared_615_ = v_isSharedCheck_638_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_gate_611_);
lean_dec(v_ref_599_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_638_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_lhsRef_617_; 
if (v_isShared_615_ == 0)
{
v_lhsRef_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_gate_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_637_, sizeof(void*)*1, v_invert_612_);
v_lhsRef_617_ = v_reuseFailAlloc_637_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v_input_619_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_lhsRef_617_);
v_input_619_ = v___x_609_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_lhsRef_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_ref_607_);
v_input_619_ = v_reuseFailAlloc_636_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
switch(v_a_592_)
{
case 0:
{
lean_object* v_ret_620_; lean_object* v___x_622_; 
v_ret_620_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(v_aig_606_, v_input_619_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_ret_620_);
v___x_622_ = v___x_604_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_ret_620_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_cache_602_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
case 1:
{
lean_object* v_ret_624_; lean_object* v___x_626_; 
v_ret_624_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(v_aig_606_, v_input_619_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_ret_624_);
v___x_626_ = v___x_604_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_ret_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_cache_602_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
case 2:
{
lean_object* v_ret_628_; lean_object* v___x_630_; 
v_ret_628_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(v_aig_606_, v_input_619_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_ret_628_);
v___x_630_ = v___x_604_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_ret_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_cache_602_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
default: 
{
lean_object* v_ret_632_; lean_object* v___x_634_; 
v_ret_632_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(v_aig_606_, v_input_619_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_ret_632_);
v___x_634_ = v___x_604_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_ret_632_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_cache_602_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
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
lean_object* v_a_641_; lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_691_; 
v_a_641_ = lean_ctor_get(v_expr_549_, 0);
v_a_642_ = lean_ctor_get(v_expr_549_, 1);
v_a_643_ = lean_ctor_get(v_expr_549_, 2);
v_isSharedCheck_691_ = !lean_is_exclusive(v_expr_549_);
if (v_isSharedCheck_691_ == 0)
{
v___x_645_ = v_expr_549_;
v_isShared_646_ = v_isSharedCheck_691_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_inc(v_a_642_);
lean_inc(v_a_641_);
lean_dec(v_expr_549_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_691_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v_result_648_; lean_object* v_cache_649_; lean_object* v_aig_650_; lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v_result_653_; lean_object* v_cache_654_; lean_object* v_aig_655_; lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v_result_658_; lean_object* v_cache_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_690_; 
v___x_647_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_548_, v_a_641_, v_cache_550_);
v_result_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_result_648_);
v_cache_649_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_cache_649_);
lean_dec_ref(v___x_647_);
v_aig_650_ = lean_ctor_get(v_result_648_, 0);
lean_inc_ref(v_aig_650_);
v_ref_651_ = lean_ctor_get(v_result_648_, 1);
lean_inc_ref(v_ref_651_);
lean_dec_ref(v_result_648_);
v___x_652_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_650_, v_a_642_, v_cache_649_);
v_result_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_result_653_);
v_cache_654_ = lean_ctor_get(v___x_652_, 1);
lean_inc_ref(v_cache_654_);
lean_dec_ref(v___x_652_);
v_aig_655_ = lean_ctor_get(v_result_653_, 0);
lean_inc_ref(v_aig_655_);
v_ref_656_ = lean_ctor_get(v_result_653_, 1);
lean_inc_ref(v_ref_656_);
lean_dec_ref(v_result_653_);
v___x_657_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v_aig_655_, v_a_643_, v_cache_654_);
v_result_658_ = lean_ctor_get(v___x_657_, 0);
v_cache_659_ = lean_ctor_get(v___x_657_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_690_ == 0)
{
v___x_661_ = v___x_657_;
v_isShared_662_ = v_isSharedCheck_690_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_cache_659_);
lean_inc(v_result_658_);
lean_dec(v___x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_690_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_aig_663_; lean_object* v_ref_664_; lean_object* v_gate_665_; uint8_t v_invert_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_689_; 
v_aig_663_ = lean_ctor_get(v_result_658_, 0);
lean_inc_ref(v_aig_663_);
v_ref_664_ = lean_ctor_get(v_result_658_, 1);
lean_inc_ref(v_ref_664_);
lean_dec_ref(v_result_658_);
v_gate_665_ = lean_ctor_get(v_ref_651_, 0);
v_invert_666_ = lean_ctor_get_uint8(v_ref_651_, sizeof(void*)*1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_ref_651_);
if (v_isSharedCheck_689_ == 0)
{
v___x_668_ = v_ref_651_;
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_gate_665_);
lean_dec(v_ref_651_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_gate_670_; uint8_t v_invert_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_688_; 
v_gate_670_ = lean_ctor_get(v_ref_656_, 0);
v_invert_671_ = lean_ctor_get_uint8(v_ref_656_, sizeof(void*)*1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_ref_656_);
if (v_isSharedCheck_688_ == 0)
{
v___x_673_ = v_ref_656_;
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_gate_670_);
lean_dec(v_ref_656_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_discrRef_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_gate_665_);
v_discrRef_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_gate_665_);
v_discrRef_676_ = v_reuseFailAlloc_687_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v_lhsRef_678_; 
lean_ctor_set_uint8(v_discrRef_676_, sizeof(void*)*1, v_invert_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_gate_670_);
v_lhsRef_678_ = v___x_668_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_gate_670_);
v_lhsRef_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v_input_680_; 
lean_ctor_set_uint8(v_lhsRef_678_, sizeof(void*)*1, v_invert_671_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 2, v_ref_664_);
lean_ctor_set(v___x_645_, 1, v_lhsRef_678_);
lean_ctor_set(v___x_645_, 0, v_discrRef_676_);
v_input_680_ = v___x_645_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_discrRef_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_lhsRef_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_ref_664_);
v_input_680_ = v_reuseFailAlloc_685_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v_ret_681_; lean_object* v___x_683_; 
v_ret_681_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(v_aig_663_, v_input_680_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_ret_681_);
v___x_683_ = v___x_661_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_ret_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_cache_659_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_692_, lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(v_m_693_, v_a_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_696_, lean_object* v_m_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(v_00_u03b2_696_, v_m_697_, v_a_698_);
lean_dec_ref(v_m_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_700_, lean_object* v_m_701_, lean_object* v_a_702_, lean_object* v_b_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(v_m_701_, v_a_702_, v_b_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_705_, lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_709_, lean_object* v_a_710_, lean_object* v_x_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_713_, lean_object* v_a_714_, lean_object* v_x_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_713_, v_a_714_, v_x_715_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_718_, lean_object* v_data_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_722_, v_b_723_, v_x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_726_, lean_object* v_i_727_, lean_object* v_source_728_, lean_object* v_target_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_727_, v_source_728_, v_target_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_732_, v_x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_unsigned_to_nat(16u);
v___x_741_ = lean_mk_array(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_746_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_748_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_box(0);
v___x_750_ = lean_unsigned_to_nat(16u);
v___x_751_ = lean_mk_array(v___x_750_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_result_759_; 
v___x_756_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_757_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_758_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(v___x_756_, v_expr_755_, v___x_757_);
v_result_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_result_759_);
lean_dec_ref(v___x_758_);
return v_result_759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* v_expr_760_, lean_object* v_h__1_761_, lean_object* v_h__2_762_, lean_object* v_h__3_763_, lean_object* v_h__4_764_, lean_object* v_h__5_765_){
_start:
{
switch(lean_obj_tag(v_expr_760_))
{
case 0:
{
lean_object* v_a_766_; lean_object* v___x_767_; 
lean_dec(v_h__5_765_);
lean_dec(v_h__4_764_);
lean_dec(v_h__3_763_);
lean_dec(v_h__2_762_);
v_a_766_ = lean_ctor_get(v_expr_760_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v_expr_760_, 1);
v___x_767_ = lean_apply_1(v_h__1_761_, v_a_766_);
return v___x_767_;
}
case 1:
{
uint8_t v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_h__5_765_);
lean_dec(v_h__4_764_);
lean_dec(v_h__3_763_);
lean_dec(v_h__1_761_);
v_a_768_ = lean_ctor_get_uint8(v_expr_760_, 0);
lean_dec_ref_known(v_expr_760_, 0);
v___x_769_ = lean_box(v_a_768_);
v___x_770_ = lean_apply_1(v_h__2_762_, v___x_769_);
return v___x_770_;
}
case 2:
{
lean_object* v_a_771_; lean_object* v___x_772_; 
lean_dec(v_h__5_765_);
lean_dec(v_h__4_764_);
lean_dec(v_h__2_762_);
lean_dec(v_h__1_761_);
v_a_771_ = lean_ctor_get(v_expr_760_, 0);
lean_inc_ref(v_a_771_);
lean_dec_ref_known(v_expr_760_, 1);
v___x_772_ = lean_apply_1(v_h__3_763_, v_a_771_);
return v___x_772_;
}
case 3:
{
uint8_t v_a_773_; lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_h__4_764_);
lean_dec(v_h__3_763_);
lean_dec(v_h__2_762_);
lean_dec(v_h__1_761_);
v_a_773_ = lean_ctor_get_uint8(v_expr_760_, sizeof(void*)*2);
v_a_774_ = lean_ctor_get(v_expr_760_, 0);
lean_inc_ref(v_a_774_);
v_a_775_ = lean_ctor_get(v_expr_760_, 1);
lean_inc_ref(v_a_775_);
lean_dec_ref_known(v_expr_760_, 2);
v___x_776_ = lean_box(v_a_773_);
v___x_777_ = lean_apply_3(v_h__5_765_, v___x_776_, v_a_774_, v_a_775_);
return v___x_777_;
}
default: 
{
lean_object* v_a_778_; lean_object* v_a_779_; lean_object* v_a_780_; lean_object* v___x_781_; 
lean_dec(v_h__5_765_);
lean_dec(v_h__3_763_);
lean_dec(v_h__2_762_);
lean_dec(v_h__1_761_);
v_a_778_ = lean_ctor_get(v_expr_760_, 0);
lean_inc_ref(v_a_778_);
v_a_779_ = lean_ctor_get(v_expr_760_, 1);
lean_inc_ref(v_a_779_);
v_a_780_ = lean_ctor_get(v_expr_760_, 2);
lean_inc_ref(v_a_780_);
lean_dec_ref_known(v_expr_760_, 3);
v___x_781_ = lean_apply_3(v_h__4_764_, v_a_778_, v_a_779_, v_a_780_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* v_motive_782_, lean_object* v_expr_783_, lean_object* v_h__1_784_, lean_object* v_h__2_785_, lean_object* v_h__3_786_, lean_object* v_h__4_787_, lean_object* v_h__5_788_){
_start:
{
switch(lean_obj_tag(v_expr_783_))
{
case 0:
{
lean_object* v_a_789_; lean_object* v___x_790_; 
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
v_a_789_ = lean_ctor_get(v_expr_783_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v_expr_783_, 1);
v___x_790_ = lean_apply_1(v_h__1_784_, v_a_789_);
return v___x_790_;
}
case 1:
{
uint8_t v_a_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__1_784_);
v_a_791_ = lean_ctor_get_uint8(v_expr_783_, 0);
lean_dec_ref_known(v_expr_783_, 0);
v___x_792_ = lean_box(v_a_791_);
v___x_793_ = lean_apply_1(v_h__2_785_, v___x_792_);
return v___x_793_;
}
case 2:
{
lean_object* v_a_794_; lean_object* v___x_795_; 
lean_dec(v_h__5_788_);
lean_dec(v_h__4_787_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_794_ = lean_ctor_get(v_expr_783_, 0);
lean_inc_ref(v_a_794_);
lean_dec_ref_known(v_expr_783_, 1);
v___x_795_ = lean_apply_1(v_h__3_786_, v_a_794_);
return v___x_795_;
}
case 3:
{
uint8_t v_a_796_; lean_object* v_a_797_; lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_h__4_787_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_796_ = lean_ctor_get_uint8(v_expr_783_, sizeof(void*)*2);
v_a_797_ = lean_ctor_get(v_expr_783_, 0);
lean_inc_ref(v_a_797_);
v_a_798_ = lean_ctor_get(v_expr_783_, 1);
lean_inc_ref(v_a_798_);
lean_dec_ref_known(v_expr_783_, 2);
v___x_799_ = lean_box(v_a_796_);
v___x_800_ = lean_apply_3(v_h__5_788_, v___x_799_, v_a_797_, v_a_798_);
return v___x_800_;
}
default: 
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v_a_803_; lean_object* v___x_804_; 
lean_dec(v_h__5_788_);
lean_dec(v_h__3_786_);
lean_dec(v_h__2_785_);
lean_dec(v_h__1_784_);
v_a_801_ = lean_ctor_get(v_expr_783_, 0);
lean_inc_ref(v_a_801_);
v_a_802_ = lean_ctor_get(v_expr_783_, 1);
lean_inc_ref(v_a_802_);
v_a_803_ = lean_ctor_get(v_expr_783_, 2);
lean_inc_ref(v_a_803_);
lean_dec_ref_known(v_expr_783_, 3);
v___x_804_ = lean_apply_3(v_h__4_787_, v_a_801_, v_a_802_, v_a_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* v_x_805_, lean_object* v_h__1_806_){
_start:
{
lean_object* v_result_807_; lean_object* v_cache_808_; lean_object* v_aig_809_; lean_object* v_ref_810_; lean_object* v___x_811_; 
v_result_807_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_result_807_);
v_cache_808_ = lean_ctor_get(v_x_805_, 1);
lean_inc_ref(v_cache_808_);
lean_dec_ref(v_x_805_);
v_aig_809_ = lean_ctor_get(v_result_807_, 0);
lean_inc_ref(v_aig_809_);
v_ref_810_ = lean_ctor_get(v_result_807_, 1);
lean_inc_ref(v_ref_810_);
lean_dec_ref(v_result_807_);
v___x_811_ = lean_apply_4(v_h__1_806_, v_aig_809_, v_ref_810_, lean_box(0), v_cache_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* v_aig_812_, lean_object* v_motive_813_, lean_object* v_x_814_, lean_object* v_h__1_815_){
_start:
{
lean_object* v_result_816_; lean_object* v_cache_817_; lean_object* v_aig_818_; lean_object* v_ref_819_; lean_object* v___x_820_; 
v_result_816_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref(v_result_816_);
v_cache_817_ = lean_ctor_get(v_x_814_, 1);
lean_inc_ref(v_cache_817_);
lean_dec_ref(v_x_814_);
v_aig_818_ = lean_ctor_get(v_result_816_, 0);
lean_inc_ref(v_aig_818_);
v_ref_819_ = lean_ctor_get(v_result_816_, 1);
lean_inc_ref(v_ref_819_);
lean_dec_ref(v_result_816_);
v___x_820_ = lean_apply_4(v_h__1_815_, v_aig_818_, v_ref_819_, lean_box(0), v_cache_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* v_aig_821_, lean_object* v_motive_822_, lean_object* v_x_823_, lean_object* v_h__1_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(v_aig_821_, v_motive_822_, v_x_823_, v_h__1_824_);
lean_dec_ref(v_aig_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t v_g_826_, lean_object* v_h__1_827_, lean_object* v_h__2_828_, lean_object* v_h__3_829_, lean_object* v_h__4_830_){
_start:
{
switch(v_g_826_)
{
case 0:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_h__4_830_);
lean_dec(v_h__3_829_);
lean_dec(v_h__2_828_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_apply_1(v_h__1_827_, v___x_831_);
return v___x_832_;
}
case 1:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_h__4_830_);
lean_dec(v_h__3_829_);
lean_dec(v_h__1_827_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_apply_1(v_h__2_828_, v___x_833_);
return v___x_834_;
}
case 2:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_h__4_830_);
lean_dec(v_h__2_828_);
lean_dec(v_h__1_827_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_apply_1(v_h__3_829_, v___x_835_);
return v___x_836_;
}
default: 
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_h__3_829_);
lean_dec(v_h__2_828_);
lean_dec(v_h__1_827_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_apply_1(v_h__4_830_, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* v_g_839_, lean_object* v_h__1_840_, lean_object* v_h__2_841_, lean_object* v_h__3_842_, lean_object* v_h__4_843_){
_start:
{
uint8_t v_g_42__boxed_844_; lean_object* v_res_845_; 
v_g_42__boxed_844_ = lean_unbox(v_g_839_);
v_res_845_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(v_g_42__boxed_844_, v_h__1_840_, v_h__2_841_, v_h__3_842_, v_h__4_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* v_motive_846_, uint8_t v_g_847_, lean_object* v_h__1_848_, lean_object* v_h__2_849_, lean_object* v_h__3_850_, lean_object* v_h__4_851_){
_start:
{
switch(v_g_847_)
{
case 0:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_h__4_851_);
lean_dec(v_h__3_850_);
lean_dec(v_h__2_849_);
v___x_852_ = lean_box(0);
v___x_853_ = lean_apply_1(v_h__1_848_, v___x_852_);
return v___x_853_;
}
case 1:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_h__4_851_);
lean_dec(v_h__3_850_);
lean_dec(v_h__1_848_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_apply_1(v_h__2_849_, v___x_854_);
return v___x_855_;
}
case 2:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v_h__4_851_);
lean_dec(v_h__2_849_);
lean_dec(v_h__1_848_);
v___x_856_ = lean_box(0);
v___x_857_ = lean_apply_1(v_h__3_850_, v___x_856_);
return v___x_857_;
}
default: 
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_h__3_850_);
lean_dec(v_h__2_849_);
lean_dec(v_h__1_848_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_1(v_h__4_851_, v___x_858_);
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* v_motive_860_, lean_object* v_g_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_, lean_object* v_h__3_864_, lean_object* v_h__4_865_){
_start:
{
uint8_t v_g_61__boxed_866_; lean_object* v_res_867_; 
v_g_61__boxed_866_ = lean_unbox(v_g_861_);
v_res_867_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(v_motive_860_, v_g_61__boxed_866_, v_h__1_862_, v_h__2_863_, v_h__3_864_, v_h__4_865_);
return v_res_867_;
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
