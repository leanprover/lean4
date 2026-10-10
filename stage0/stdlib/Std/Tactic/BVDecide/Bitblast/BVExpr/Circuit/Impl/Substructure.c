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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_10_, v_x_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_a_14_, lean_object* v_b_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_dec(v_b_15_);
lean_dec(v_a_14_);
return v_x_16_;
}
else
{
lean_object* v_key_17_; lean_object* v_value_18_; lean_object* v_tail_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_32_; 
v_key_17_ = lean_ctor_get(v_x_16_, 0);
v_value_18_ = lean_ctor_get(v_x_16_, 1);
v_tail_19_ = lean_ctor_get(v_x_16_, 2);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_32_ == 0)
{
v___x_21_ = v_x_16_;
v_isShared_22_ = v_isSharedCheck_32_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_tail_19_);
lean_inc(v_value_18_);
lean_inc(v_key_17_);
lean_dec(v_x_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_32_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_14_);
lean_inc(v_key_17_);
v___x_24_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_23_, v_key_17_, v_a_14_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_14_, v_b_15_, v_tail_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_25_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_key_17_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_value_18_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
else
{
lean_object* v___x_30_; 
lean_dec(v_value_18_);
lean_dec(v_key_17_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v_b_15_);
lean_ctor_set(v___x_21_, 0, v_a_14_);
v___x_30_ = v___x_21_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_14_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_b_15_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_tail_19_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_33_){
_start:
{
switch(lean_obj_tag(v_x_33_))
{
case 0:
{
uint64_t v___x_34_; 
v___x_34_ = 0ULL;
return v___x_34_;
}
case 1:
{
lean_object* v_idx_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; 
v_idx_35_ = lean_ctor_get(v_x_33_, 0);
v___x_36_ = 1ULL;
v___x_37_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_35_);
v___x_38_ = lean_uint64_mix_hash(v___x_36_, v___x_37_);
return v___x_38_;
}
default: 
{
lean_object* v_l_39_; lean_object* v_r_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; 
v_l_39_ = lean_ctor_get(v_x_33_, 0);
v_r_40_ = lean_ctor_get(v_x_33_, 1);
v___x_41_ = 2ULL;
v___x_42_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_39_);
v___x_43_ = lean_uint64_mix_hash(v___x_41_, v___x_42_);
v___x_44_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_40_);
v___x_45_ = lean_uint64_mix_hash(v___x_43_, v___x_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_33_ = stack[0].m_obj;
uint64_t v_res_46_;
v_res_46_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_x_33_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_x_47_){
_start:
{
uint64_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_x_47_);
lean_dec(v_x_47_);
v_r_49_ = lean_box_uint64(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
return v_x_50_;
}
else
{
lean_object* v_key_52_; lean_object* v_value_53_; lean_object* v_tail_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_77_; 
v_key_52_ = lean_ctor_get(v_x_51_, 0);
v_value_53_ = lean_ctor_get(v_x_51_, 1);
v_tail_54_ = lean_ctor_get(v_x_51_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_77_ == 0)
{
v___x_56_ = v_x_51_;
v_isShared_57_ = v_isSharedCheck_77_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_tail_54_);
lean_inc(v_value_53_);
lean_inc(v_key_52_);
lean_dec(v_x_51_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_77_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v___x_61_; uint64_t v_fold_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; size_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_58_ = lean_array_get_size(v_x_50_);
v___x_59_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_key_52_);
v___x_60_ = 32ULL;
v___x_61_ = lean_uint64_shift_right(v___x_59_, v___x_60_);
v_fold_62_ = lean_uint64_xor(v___x_59_, v___x_61_);
v___x_63_ = 16ULL;
v___x_64_ = lean_uint64_shift_right(v_fold_62_, v___x_63_);
v___x_65_ = lean_uint64_xor(v_fold_62_, v___x_64_);
v___x_66_ = lean_uint64_to_usize(v___x_65_);
v___x_67_ = lean_usize_of_nat(v___x_58_);
v___x_68_ = ((size_t)1ULL);
v___x_69_ = lean_usize_sub(v___x_67_, v___x_68_);
v___x_70_ = lean_usize_land(v___x_66_, v___x_69_);
v___x_71_ = lean_array_uget_borrowed(v_x_50_, v___x_70_);
lean_inc(v___x_71_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 2, v___x_71_);
v___x_73_ = v___x_56_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_key_52_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_value_53_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_array_uset(v_x_50_, v___x_70_, v___x_73_);
v_x_50_ = v___x_74_;
v_x_51_ = v_tail_54_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object* v_i_78_, lean_object* v_source_79_, lean_object* v_target_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_array_get_size(v_source_79_);
v___x_82_ = lean_nat_dec_lt(v_i_78_, v___x_81_);
if (v___x_82_ == 0)
{
lean_dec_ref(v_source_79_);
lean_dec(v_i_78_);
return v_target_80_;
}
else
{
lean_object* v_es_83_; lean_object* v___x_84_; lean_object* v_source_85_; lean_object* v_target_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_es_83_ = lean_array_fget(v_source_79_, v_i_78_);
v___x_84_ = lean_box(0);
v_source_85_ = lean_array_fset(v_source_79_, v_i_78_, v___x_84_);
v_target_86_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_target_80_, v_es_83_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_78_, v___x_87_);
lean_dec(v_i_78_);
v_i_78_ = v___x_88_;
v_source_79_ = v_source_85_;
v_target_80_ = v_target_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_data_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_nbuckets_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_91_ = lean_array_get_size(v_data_90_);
v___x_92_ = lean_unsigned_to_nat(2u);
v_nbuckets_93_ = lean_nat_mul(v___x_91_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_box(0);
v___x_96_ = lean_mk_array(v_nbuckets_93_, v___x_95_);
v___x_97_ = lean_array_propagate_mark(v_data_90_, v___x_96_);
v___x_98_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v___x_94_, v_data_90_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(lean_object* v_m_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_size_102_; lean_object* v_buckets_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_146_; 
v_size_102_ = lean_ctor_get(v_m_99_, 0);
v_buckets_103_ = lean_ctor_get(v_m_99_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_m_99_);
if (v_isSharedCheck_146_ == 0)
{
v___x_105_ = v_m_99_;
v_isShared_106_ = v_isSharedCheck_146_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_buckets_103_);
lean_inc(v_size_102_);
lean_dec(v_m_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_146_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v_fold_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v_bkt_120_; uint8_t v___x_121_; 
v___x_107_ = lean_array_get_size(v_buckets_103_);
v___x_108_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_a_100_);
v___x_109_ = 32ULL;
v___x_110_ = lean_uint64_shift_right(v___x_108_, v___x_109_);
v_fold_111_ = lean_uint64_xor(v___x_108_, v___x_110_);
v___x_112_ = 16ULL;
v___x_113_ = lean_uint64_shift_right(v_fold_111_, v___x_112_);
v___x_114_ = lean_uint64_xor(v_fold_111_, v___x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = lean_usize_of_nat(v___x_107_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_sub(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_land(v___x_115_, v___x_118_);
v_bkt_120_ = lean_array_uget_borrowed(v_buckets_103_, v___x_119_);
lean_inc(v_bkt_120_);
lean_inc(v_a_100_);
v___x_121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_100_, v_bkt_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v_size_x27_123_; lean_object* v___x_124_; lean_object* v_buckets_x27_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v_size_x27_123_ = lean_nat_add(v_size_102_, v___x_122_);
lean_dec(v_size_102_);
lean_inc(v_bkt_120_);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v_a_100_);
lean_ctor_set(v___x_124_, 1, v_b_101_);
lean_ctor_set(v___x_124_, 2, v_bkt_120_);
v_buckets_x27_125_ = lean_array_uset(v_buckets_103_, v___x_119_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(4u);
v___x_127_ = lean_nat_mul(v_size_x27_123_, v___x_126_);
v___x_128_ = lean_unsigned_to_nat(3u);
v___x_129_ = lean_nat_div(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_array_get_size(v_buckets_x27_125_);
v___x_131_ = lean_nat_dec_le(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
if (v___x_131_ == 0)
{
lean_object* v_val_132_; lean_object* v___x_134_; 
v_val_132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(v_buckets_x27_125_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_val_132_);
lean_ctor_set(v___x_105_, 0, v_size_x27_123_);
v___x_134_ = v___x_105_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_val_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_137_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_buckets_x27_125_);
lean_ctor_set(v___x_105_, 0, v_size_x27_123_);
v___x_137_ = v___x_105_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_size_x27_123_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_buckets_x27_125_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v___x_139_; lean_object* v_buckets_x27_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc(v_bkt_120_);
v___x_139_ = lean_box(0);
v_buckets_x27_140_ = lean_array_uset(v_buckets_103_, v___x_119_, v___x_139_);
v___x_141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_100_, v_b_101_, v_bkt_120_);
v___x_142_ = lean_array_uset(v_buckets_x27_140_, v___x_119_, v___x_141_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_142_);
v___x_144_ = v___x_105_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_size_102_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v___x_149_; 
lean_dec(v_a_147_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
lean_object* v_key_150_; lean_object* v_value_151_; lean_object* v_tail_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_key_150_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_key_150_);
v_value_151_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_value_151_);
v_tail_152_ = lean_ctor_get(v_x_148_, 2);
lean_inc(v_tail_152_);
lean_dec_ref_known(v_x_148_, 3);
v___x_153_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_147_);
v___x_154_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_153_, v_key_150_, v_a_147_);
if (v___x_154_ == 0)
{
lean_dec(v_value_151_);
v_x_148_ = v_tail_152_;
goto _start;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_tail_152_);
lean_dec(v_a_147_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_value_151_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_buckets_159_; lean_object* v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v_fold_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_buckets_159_ = lean_ctor_get(v_m_157_, 1);
v___x_160_ = lean_array_get_size(v_buckets_159_);
v___x_161_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__6(v_a_158_);
v___x_162_ = 32ULL;
v___x_163_ = lean_uint64_shift_right(v___x_161_, v___x_162_);
v_fold_164_ = lean_uint64_xor(v___x_161_, v___x_163_);
v___x_165_ = 16ULL;
v___x_166_ = lean_uint64_shift_right(v_fold_164_, v___x_165_);
v___x_167_ = lean_uint64_xor(v_fold_164_, v___x_166_);
v___x_168_ = lean_uint64_to_usize(v___x_167_);
v___x_169_ = lean_usize_of_nat(v___x_160_);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_sub(v___x_169_, v___x_170_);
v___x_172_ = lean_usize_land(v___x_168_, v___x_171_);
v___x_173_ = lean_array_uget_borrowed(v_buckets_159_, v___x_172_);
lean_inc(v___x_173_);
v___x_174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_158_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_m_175_, v_a_176_);
lean_dec_ref(v_m_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(lean_object* v_aig_178_, lean_object* v_ref_179_){
_start:
{
lean_object* v_gate_180_; uint8_t v_invert_181_; lean_object* v_decls_182_; lean_object* v_decl_183_; 
v_gate_180_ = lean_ctor_get(v_ref_179_, 0);
v_invert_181_ = lean_ctor_get_uint8(v_ref_179_, sizeof(void*)*1);
v_decls_182_ = lean_ctor_get(v_aig_178_, 0);
v_decl_183_ = lean_array_fget_borrowed(v_decls_182_, v_gate_180_);
if (lean_obj_tag(v_decl_183_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(v_invert_181_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2___boxed(lean_object* v_aig_187_, lean_object* v_ref_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v_aig_187_, v_ref_188_);
lean_dec_ref(v_ref_188_);
lean_dec_ref(v_aig_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(lean_object* v_aig_193_, lean_object* v_input_194_){
_start:
{
lean_object* v_lhs_195_; lean_object* v_rhs_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_279_; 
v_lhs_195_ = lean_ctor_get(v_input_194_, 0);
v_rhs_196_ = lean_ctor_get(v_input_194_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_input_194_);
if (v_isSharedCheck_279_ == 0)
{
v___x_198_ = v_input_194_;
v_isShared_199_ = v_isSharedCheck_279_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_rhs_196_);
lean_inc(v_lhs_195_);
lean_dec(v_input_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_279_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_decls_200_; lean_object* v_cache_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_278_; 
v_decls_200_ = lean_ctor_get(v_aig_193_, 0);
v_cache_201_ = lean_ctor_get(v_aig_193_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_aig_193_);
if (v_isSharedCheck_278_ == 0)
{
v___x_203_ = v_aig_193_;
v_isShared_204_ = v_isSharedCheck_278_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_cache_201_);
lean_inc(v_decls_200_);
lean_dec(v_aig_193_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_278_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_gate_205_; uint8_t v_invert_206_; lean_object* v_gate_207_; uint8_t v_invert_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_decl_217_; 
v_gate_205_ = lean_ctor_get(v_lhs_195_, 0);
lean_inc(v_gate_205_);
v_invert_206_ = lean_ctor_get_uint8(v_lhs_195_, sizeof(void*)*1);
v_gate_207_ = lean_ctor_get(v_rhs_196_, 0);
v_invert_208_ = lean_ctor_get_uint8(v_rhs_196_, sizeof(void*)*1);
v___x_209_ = lean_unsigned_to_nat(2u);
v___x_210_ = lean_nat_mul(v_gate_205_, v___x_209_);
v___x_211_ = l_Bool_toNat(v_invert_206_);
v___x_212_ = lean_nat_lor(v___x_210_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_nat_mul(v_gate_207_, v___x_209_);
v___x_214_ = l_Bool_toNat(v_invert_208_);
v___x_215_ = lean_nat_lor(v___x_213_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v___x_213_);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 2);
lean_ctor_set(v___x_198_, 1, v___x_215_);
lean_ctor_set(v___x_198_, 0, v___x_212_);
v_decl_217_ = v___x_198_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_215_);
v_decl_217_ = v_reuseFailAlloc_277_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
lean_inc_ref(v_decl_217_);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_cache_201_, v_decl_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_220_; 
lean_inc(v_gate_207_);
lean_inc_ref(v_cache_201_);
lean_inc_ref(v_decls_200_);
if (v_isShared_204_ == 0)
{
v___x_220_ = v___x_203_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_decls_200_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_cache_201_);
v___x_220_ = v_reuseFailAlloc_262_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
uint8_t v___y_222_; uint8_t v___y_227_; lean_object* v_lhsVal_236_; lean_object* v_rhsVal_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
v_lhsVal_236_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_220_, v_lhs_195_);
lean_dec_ref(v_lhs_195_);
v_rhsVal_237_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__2(v___x_220_, v_rhs_196_);
v_isSharedCheck_260_ = !lean_is_exclusive(v_rhs_196_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v_rhs_196_, 0);
lean_dec(v_unused_261_);
v___x_239_ = v_rhs_196_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_rhs_196_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v_ref_224_; lean_object* v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v_ref_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_224_, 0, v___x_223_);
lean_ctor_set_uint8(v_ref_224_, sizeof(void*)*1, v___y_222_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_220_);
lean_ctor_set(v___x_225_, 1, v_ref_224_);
return v___x_225_;
}
v___jp_226_:
{
if (v___y_227_ == 0)
{
lean_dec(v_gate_205_);
v___y_222_ = v___y_227_;
goto v___jp_221_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_228_, 0, v_gate_205_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v_invert_206_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_220_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_231_, 0, v_gate_207_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v_invert_208_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_220_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
v___jp_233_:
{
lean_object* v_ref_234_; lean_object* v___x_235_; 
v_ref_234_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0___closed__0));
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_220_);
lean_ctor_set(v___x_235_, 1, v_ref_234_);
return v___x_235_;
}
v_resetjp_238_:
{
if (lean_obj_tag(v_lhsVal_236_) == 1)
{
lean_object* v_val_241_; uint8_t v___x_242_; 
lean_del_object(v___x_239_);
lean_dec_ref(v_decl_217_);
lean_dec(v_gate_205_);
lean_dec_ref(v_cache_201_);
lean_dec_ref(v_decls_200_);
v_val_241_ = lean_ctor_get(v_lhsVal_236_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v_lhsVal_236_, 1);
v___x_242_ = lean_unbox(v_val_241_);
lean_dec(v_val_241_);
if (v___x_242_ == 0)
{
lean_dec(v_rhsVal_237_);
lean_dec(v_gate_207_);
goto v___jp_233_;
}
else
{
if (lean_obj_tag(v_rhsVal_237_) == 1)
{
lean_object* v_val_243_; uint8_t v___x_244_; 
v_val_243_ = lean_ctor_get(v_rhsVal_237_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v_rhsVal_237_, 1);
v___x_244_ = lean_unbox(v_val_243_);
lean_dec(v_val_243_);
if (v___x_244_ == 0)
{
lean_dec(v_gate_207_);
goto v___jp_233_;
}
else
{
goto v___jp_230_;
}
}
else
{
lean_dec(v_rhsVal_237_);
goto v___jp_230_;
}
}
}
else
{
lean_dec(v_lhsVal_236_);
if (lean_obj_tag(v_rhsVal_237_) == 1)
{
lean_object* v_val_245_; uint8_t v___x_246_; 
lean_dec_ref(v_decl_217_);
lean_dec(v_gate_207_);
lean_dec_ref(v_cache_201_);
lean_dec_ref(v_decls_200_);
v_val_245_ = lean_ctor_get(v_rhsVal_237_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_rhsVal_237_, 1);
v___x_246_ = lean_unbox(v_val_245_);
lean_dec(v_val_245_);
if (v___x_246_ == 0)
{
lean_del_object(v___x_239_);
lean_dec(v_gate_205_);
goto v___jp_233_;
}
else
{
lean_object* v___x_248_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_gate_205_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_gate_205_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*1, v_invert_206_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_220_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
}
else
{
uint8_t v___x_251_; 
lean_dec(v_rhsVal_237_);
v___x_251_ = lean_nat_dec_eq(v_gate_205_, v_gate_207_);
lean_dec(v_gate_207_);
if (v___x_251_ == 0)
{
lean_object* v_g_252_; lean_object* v_cache_253_; lean_object* v_decls_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec_ref(v___x_220_);
lean_dec(v_gate_205_);
v_g_252_ = lean_array_get_size(v_decls_200_);
lean_inc_ref(v_decl_217_);
v_cache_253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_cache_201_, v_decl_217_, v_g_252_);
v_decls_254_ = lean_array_push(v_decls_200_, v_decl_217_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_decls_254_);
lean_ctor_set(v___x_255_, 1, v_cache_253_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_g_252_);
v___x_257_ = v___x_239_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_g_252_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_251_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_255_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
}
else
{
lean_del_object(v___x_239_);
lean_dec_ref(v_decl_217_);
lean_dec_ref(v_cache_201_);
lean_dec_ref(v_decls_200_);
if (v_invert_208_ == 0)
{
if (v_invert_206_ == 0)
{
v___y_227_ = v___x_251_;
goto v___jp_226_;
}
else
{
lean_dec(v_gate_205_);
v___y_222_ = v_invert_208_;
goto v___jp_221_;
}
}
else
{
v___y_227_ = v_invert_206_;
goto v___jp_226_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v_decl_217_);
lean_dec(v_gate_205_);
lean_dec_ref(v_lhs_195_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_rhs_196_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_rhs_196_, 0);
lean_dec(v_unused_276_);
v___x_264_ = v_rhs_196_;
v_isShared_265_ = v_isSharedCheck_275_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_rhs_196_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_275_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_val_266_; lean_object* v___x_268_; 
v_val_266_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_218_, 1);
if (v_isShared_204_ == 0)
{
v___x_268_ = v___x_203_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_decls_200_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_cache_201_);
v___x_268_ = v_reuseFailAlloc_274_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
uint8_t v___x_269_; lean_object* v___x_271_; 
v___x_269_ = 0;
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v_val_266_);
v___x_271_ = v___x_264_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_val_266_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_269_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_268_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(lean_object* v_aig_280_, lean_object* v_input_281_){
_start:
{
lean_object* v_lhs_282_; lean_object* v_rhs_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_298_; 
v_lhs_282_ = lean_ctor_get(v_input_281_, 0);
v_rhs_283_ = lean_ctor_get(v_input_281_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_input_281_);
if (v_isSharedCheck_298_ == 0)
{
v___x_285_ = v_input_281_;
v_isShared_286_ = v_isSharedCheck_298_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_rhs_283_);
lean_inc(v_lhs_282_);
lean_dec(v_input_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_298_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_gate_287_; lean_object* v_gate_288_; uint8_t v___x_289_; 
v_gate_287_ = lean_ctor_get(v_lhs_282_, 0);
v_gate_288_ = lean_ctor_get(v_rhs_283_, 0);
v___x_289_ = lean_nat_dec_lt(v_gate_287_, v_gate_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_291_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_lhs_282_);
lean_ctor_set(v___x_285_, 0, v_rhs_283_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_rhs_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_lhs_282_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_280_, v___x_291_);
return v___x_292_;
}
}
else
{
lean_object* v___x_295_; 
if (v_isShared_286_ == 0)
{
v___x_295_ = v___x_285_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_lhs_282_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_rhs_283_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0(v_aig_280_, v___x_295_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object* v_aig_299_, lean_object* v_input_300_){
_start:
{
lean_object* v___y_302_; lean_object* v_lhs_342_; lean_object* v_rhs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_387_; 
v_lhs_342_ = lean_ctor_get(v_input_300_, 0);
v_rhs_343_ = lean_ctor_get(v_input_300_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_input_300_);
if (v_isSharedCheck_387_ == 0)
{
v___x_345_ = v_input_300_;
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_rhs_343_);
lean_inc(v_lhs_342_);
lean_dec(v_input_300_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
v___jp_301_:
{
lean_object* v_res_303_; lean_object* v_ref_304_; uint8_t v_invert_305_; 
v_res_303_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_299_, v___y_302_);
v_ref_304_ = lean_ctor_get(v_res_303_, 1);
lean_inc_ref(v_ref_304_);
v_invert_305_ = lean_ctor_get_uint8(v_ref_304_, sizeof(void*)*1);
if (v_invert_305_ == 0)
{
lean_object* v_aig_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_322_; 
v_aig_306_ = lean_ctor_get(v_res_303_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_res_303_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_res_303_, 1);
lean_dec(v_unused_323_);
v___x_308_ = v_res_303_;
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_aig_306_);
lean_dec(v_res_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_gate_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_321_; 
v_gate_310_ = lean_ctor_get(v_ref_304_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_ref_304_);
if (v_isSharedCheck_321_ == 0)
{
v___x_312_ = v_ref_304_;
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_gate_310_);
lean_dec(v_ref_304_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; lean_object* v___x_316_; 
v___x_314_ = 1;
if (v_isShared_313_ == 0)
{
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_gate_310_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_314_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_316_);
v___x_318_ = v___x_308_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_aig_306_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
else
{
lean_object* v_aig_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_340_; 
v_aig_324_ = lean_ctor_get(v_res_303_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_res_303_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_res_303_, 1);
lean_dec(v_unused_341_);
v___x_326_ = v_res_303_;
v_isShared_327_ = v_isSharedCheck_340_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_aig_324_);
lean_dec(v_res_303_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_340_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_gate_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
v_gate_328_ = lean_ctor_get(v_ref_304_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_ref_304_);
if (v_isSharedCheck_339_ == 0)
{
v___x_330_ = v_ref_304_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_gate_328_);
lean_dec(v_ref_304_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint8_t v___x_332_; lean_object* v___x_334_; 
v___x_332_ = 0;
if (v_isShared_331_ == 0)
{
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_gate_328_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_332_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_334_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_aig_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
v_resetjp_344_:
{
lean_object* v_gate_347_; uint8_t v_invert_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_386_; 
v_gate_347_ = lean_ctor_get(v_lhs_342_, 0);
v_invert_348_ = lean_ctor_get_uint8(v_lhs_342_, sizeof(void*)*1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_lhs_342_);
if (v_isSharedCheck_386_ == 0)
{
v___x_350_ = v_lhs_342_;
v_isShared_351_ = v_isSharedCheck_386_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_gate_347_);
lean_dec(v_lhs_342_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_386_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; lean_object* v___y_354_; 
v___x_352_ = 1;
if (v_invert_348_ == 0)
{
lean_object* v___x_380_; 
if (v_isShared_351_ == 0)
{
v___x_380_ = v___x_350_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_gate_347_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_352_);
v___y_354_ = v___x_380_;
goto v___jp_353_;
}
}
else
{
uint8_t v___x_382_; lean_object* v___x_384_; 
v___x_382_ = 0;
if (v_isShared_351_ == 0)
{
v___x_384_ = v___x_350_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_gate_347_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*1, v___x_382_);
v___y_354_ = v___x_384_;
goto v___jp_353_;
}
}
v___jp_353_:
{
uint8_t v_invert_355_; 
v_invert_355_ = lean_ctor_get_uint8(v_rhs_343_, sizeof(void*)*1);
if (v_invert_355_ == 0)
{
lean_object* v_gate_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_gate_356_ = lean_ctor_get(v_rhs_343_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_rhs_343_);
if (v_isSharedCheck_366_ == 0)
{
v___x_358_ = v_rhs_343_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_gate_356_);
lean_dec(v_rhs_343_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
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
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_gate_356_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_352_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_361_);
lean_ctor_set(v___x_345_, 0, v___y_354_);
v___x_363_ = v___x_345_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___y_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v___y_302_ = v___x_363_;
goto v___jp_301_;
}
}
}
}
else
{
lean_object* v_gate_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_378_; 
v_gate_367_ = lean_ctor_get(v_rhs_343_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_rhs_343_);
if (v_isSharedCheck_378_ == 0)
{
v___x_369_ = v_rhs_343_;
v_isShared_370_ = v_isSharedCheck_378_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_gate_367_);
lean_dec(v_rhs_343_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_378_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___x_371_; lean_object* v___x_373_; 
v___x_371_ = 0;
if (v_isShared_370_ == 0)
{
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_gate_367_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_371_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_373_);
lean_ctor_set(v___x_345_, 0, v___y_354_);
v___x_375_ = v___x_345_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___y_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v___y_302_ = v___x_375_;
goto v___jp_301_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object* v_aig_388_, lean_object* v_input_389_){
_start:
{
lean_object* v_discr_390_; lean_object* v_lhs_391_; lean_object* v_rhs_392_; lean_object* v___x_393_; lean_object* v_res_394_; lean_object* v_aig_395_; lean_object* v_ref_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_449_; 
v_discr_390_ = lean_ctor_get(v_input_389_, 0);
lean_inc_ref_n(v_discr_390_, 2);
v_lhs_391_ = lean_ctor_get(v_input_389_, 1);
lean_inc_ref(v_lhs_391_);
v_rhs_392_ = lean_ctor_get(v_input_389_, 2);
lean_inc_ref(v_rhs_392_);
lean_dec_ref(v_input_389_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_discr_390_);
lean_ctor_set(v___x_393_, 1, v_lhs_391_);
v_res_394_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_388_, v___x_393_);
v_aig_395_ = lean_ctor_get(v_res_394_, 0);
v_ref_396_ = lean_ctor_get(v_res_394_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_res_394_);
if (v_isSharedCheck_449_ == 0)
{
v___x_398_ = v_res_394_;
v_isShared_399_ = v_isSharedCheck_449_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_ref_396_);
lean_inc(v_aig_395_);
lean_dec(v_res_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_449_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_gate_400_; uint8_t v_invert_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_448_; 
v_gate_400_ = lean_ctor_get(v_discr_390_, 0);
v_invert_401_ = lean_ctor_get_uint8(v_discr_390_, sizeof(void*)*1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_discr_390_);
if (v_isSharedCheck_448_ == 0)
{
v___x_403_ = v_discr_390_;
v_isShared_404_ = v_isSharedCheck_448_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_gate_400_);
lean_dec(v_discr_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_448_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_gate_405_; uint8_t v_invert_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_447_; 
v_gate_405_ = lean_ctor_get(v_rhs_392_, 0);
v_invert_406_ = lean_ctor_get_uint8(v_rhs_392_, sizeof(void*)*1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_rhs_392_);
if (v_isSharedCheck_447_ == 0)
{
v___x_408_ = v_rhs_392_;
v_isShared_409_ = v_isSharedCheck_447_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_gate_405_);
lean_dec(v_rhs_392_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_447_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_aig_411_; lean_object* v_ref_412_; 
if (v_invert_401_ == 0)
{
uint8_t v___x_439_; lean_object* v___x_441_; 
v___x_439_ = 1;
if (v_isShared_404_ == 0)
{
v___x_441_ = v___x_403_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_gate_400_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___x_439_);
v_aig_411_ = v_aig_395_;
v_ref_412_ = v___x_441_;
goto v___jp_410_;
}
}
else
{
uint8_t v___x_443_; lean_object* v___x_445_; 
v___x_443_ = 0;
if (v_isShared_404_ == 0)
{
v___x_445_ = v___x_403_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_gate_400_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_443_);
v_aig_411_ = v_aig_395_;
v_ref_412_ = v___x_445_;
goto v___jp_410_;
}
}
v___jp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_409_ == 0)
{
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_gate_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*1, v_invert_406_);
v___x_414_ = v_reuseFailAlloc_438_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_414_);
lean_ctor_set(v___x_398_, 0, v_ref_412_);
v___x_416_ = v___x_398_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_ref_412_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_414_);
v___x_416_ = v_reuseFailAlloc_437_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v_res_417_; lean_object* v_aig_418_; lean_object* v_ref_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_436_; 
v_res_417_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_411_, v___x_416_);
v_aig_418_ = lean_ctor_get(v_res_417_, 0);
v_ref_419_ = lean_ctor_get(v_res_417_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_res_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_421_ = v_res_417_;
v_isShared_422_ = v_isSharedCheck_436_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_ref_419_);
lean_inc(v_aig_418_);
lean_dec(v_res_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_436_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_gate_423_; uint8_t v_invert_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_435_; 
v_gate_423_ = lean_ctor_get(v_ref_396_, 0);
v_invert_424_ = lean_ctor_get_uint8(v_ref_396_, sizeof(void*)*1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_ref_396_);
if (v_isSharedCheck_435_ == 0)
{
v___x_426_ = v_ref_396_;
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_gate_423_);
lean_dec(v_ref_396_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_lhsRef_429_; 
if (v_isShared_427_ == 0)
{
v_lhsRef_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_gate_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*1, v_invert_424_);
v_lhsRef_429_ = v_reuseFailAlloc_434_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_lhsRef_429_);
v___x_431_ = v___x_421_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_lhsRef_429_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_ref_419_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_418_, v___x_431_);
return v___x_432_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(lean_object* v_aig_450_, lean_object* v_input_451_){
_start:
{
lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v_lhs_458_; lean_object* v_rhs_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_572_; 
v_lhs_458_ = lean_ctor_get(v_input_451_, 0);
v_rhs_459_ = lean_ctor_get(v_input_451_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_input_451_);
if (v_isSharedCheck_572_ == 0)
{
v___x_461_ = v_input_451_;
v_isShared_462_ = v_isSharedCheck_572_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_rhs_459_);
lean_inc(v_lhs_458_);
lean_dec(v_input_451_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_572_;
goto v_resetjp_460_;
}
v___jp_452_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___y_455_);
v___x_457_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_453_, v___x_456_);
return v___x_457_;
}
v_resetjp_460_:
{
lean_object* v_gate_463_; uint8_t v_invert_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_571_; 
v_gate_463_ = lean_ctor_get(v_lhs_458_, 0);
v_invert_464_ = lean_ctor_get_uint8(v_lhs_458_, sizeof(void*)*1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_lhs_458_);
if (v_isSharedCheck_571_ == 0)
{
v___x_466_ = v_lhs_458_;
v_isShared_467_ = v_isSharedCheck_571_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_gate_463_);
lean_dec(v_lhs_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_571_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; uint8_t v___x_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_536_; lean_object* v___y_561_; 
v___x_468_ = 0;
v___x_469_ = 1;
if (v_invert_464_ == 0)
{
lean_object* v___x_569_; 
lean_inc(v_gate_463_);
v___x_569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_569_, 0, v_gate_463_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*1, v___x_468_);
v___y_561_ = v___x_569_;
goto v___jp_560_;
}
else
{
lean_object* v___x_570_; 
lean_inc(v_gate_463_);
v___x_570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_570_, 0, v_gate_463_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*1, v___x_469_);
v___y_561_ = v___x_570_;
goto v___jp_560_;
}
v___jp_470_:
{
uint8_t v_invert_474_; 
v_invert_474_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*1);
if (v_invert_474_ == 0)
{
lean_object* v_gate_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_gate_475_ = lean_ctor_get(v___y_471_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___y_471_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___y_471_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_gate_475_);
lean_dec(v___y_471_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_gate_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_469_);
v___y_453_ = v___y_472_;
v___y_454_ = v___y_473_;
v___y_455_ = v___x_480_;
goto v___jp_452_;
}
}
}
else
{
lean_object* v_gate_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_gate_483_ = lean_ctor_get(v___y_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___y_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___y_471_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_gate_483_);
lean_dec(v___y_471_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_gate_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*1, v___x_468_);
v___y_453_ = v___y_472_;
v___y_454_ = v___y_473_;
v___y_455_ = v___x_488_;
goto v___jp_452_;
}
}
}
}
v___jp_491_:
{
lean_object* v_res_495_; uint8_t v_invert_496_; 
v_res_495_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_493_, v___y_494_);
v_invert_496_ = lean_ctor_get_uint8(v___y_492_, sizeof(void*)*1);
if (v_invert_496_ == 0)
{
lean_object* v_aig_497_; lean_object* v_ref_498_; lean_object* v_gate_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_aig_497_ = lean_ctor_get(v_res_495_, 0);
lean_inc_ref(v_aig_497_);
v_ref_498_ = lean_ctor_get(v_res_495_, 1);
lean_inc_ref(v_ref_498_);
lean_dec_ref(v_res_495_);
v_gate_499_ = lean_ctor_get(v___y_492_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___y_492_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___y_492_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_gate_499_);
lean_dec(v___y_492_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_gate_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_469_);
v___y_471_ = v_ref_498_;
v___y_472_ = v_aig_497_;
v___y_473_ = v___x_504_;
goto v___jp_470_;
}
}
}
else
{
lean_object* v_aig_507_; lean_object* v_ref_508_; lean_object* v_gate_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_aig_507_ = lean_ctor_get(v_res_495_, 0);
lean_inc_ref(v_aig_507_);
v_ref_508_ = lean_ctor_get(v_res_495_, 1);
lean_inc_ref(v_ref_508_);
lean_dec_ref(v_res_495_);
v_gate_509_ = lean_ctor_get(v___y_492_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___y_492_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___y_492_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_gate_509_);
lean_dec(v___y_492_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_gate_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_468_);
v___y_471_ = v_ref_508_;
v___y_472_ = v_aig_507_;
v___y_473_ = v___x_514_;
goto v___jp_470_;
}
}
}
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_524_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___y_521_);
v___x_524_ = v___x_466_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___y_521_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_468_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_524_);
lean_ctor_set(v___x_461_, 0, v___y_522_);
v___x_526_ = v___x_461_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_492_ = v___y_520_;
v___y_493_ = v___y_519_;
v___y_494_ = v___x_526_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v___x_530_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___y_521_);
v___x_530_ = v___x_466_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___y_521_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_469_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_530_);
lean_ctor_set(v___x_461_, 0, v___y_522_);
v___x_532_ = v___x_461_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_492_ = v___y_520_;
v___y_493_ = v___y_519_;
v___y_494_ = v___x_532_;
goto v___jp_491_;
}
}
}
}
v___jp_535_:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_450_, v___y_536_);
if (v_invert_464_ == 0)
{
lean_object* v_aig_538_; lean_object* v_ref_539_; lean_object* v_gate_540_; uint8_t v_invert_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_aig_538_ = lean_ctor_get(v_res_537_, 0);
lean_inc_ref(v_aig_538_);
v_ref_539_ = lean_ctor_get(v_res_537_, 1);
lean_inc_ref(v_ref_539_);
lean_dec_ref(v_res_537_);
v_gate_540_ = lean_ctor_get(v_rhs_459_, 0);
v_invert_541_ = lean_ctor_get_uint8(v_rhs_459_, sizeof(void*)*1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_rhs_459_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v_rhs_459_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_gate_540_);
lean_dec(v_rhs_459_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_gate_463_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_gate_463_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_469_);
v___y_518_ = v_invert_541_;
v___y_519_ = v_aig_538_;
v___y_520_ = v_ref_539_;
v___y_521_ = v_gate_540_;
v___y_522_ = v___x_546_;
goto v___jp_517_;
}
}
}
else
{
lean_object* v_aig_549_; lean_object* v_ref_550_; lean_object* v_gate_551_; uint8_t v_invert_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_aig_549_ = lean_ctor_get(v_res_537_, 0);
lean_inc_ref(v_aig_549_);
v_ref_550_ = lean_ctor_get(v_res_537_, 1);
lean_inc_ref(v_ref_550_);
lean_dec_ref(v_res_537_);
v_gate_551_ = lean_ctor_get(v_rhs_459_, 0);
v_invert_552_ = lean_ctor_get_uint8(v_rhs_459_, sizeof(void*)*1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_rhs_459_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v_rhs_459_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_gate_551_);
lean_dec(v_rhs_459_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v_gate_463_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_gate_463_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v___x_468_);
v___y_518_ = v_invert_552_;
v___y_519_ = v_aig_549_;
v___y_520_ = v_ref_550_;
v___y_521_ = v_gate_551_;
v___y_522_ = v___x_557_;
goto v___jp_517_;
}
}
}
}
v___jp_560_:
{
uint8_t v_invert_562_; 
v_invert_562_ = lean_ctor_get_uint8(v_rhs_459_, sizeof(void*)*1);
if (v_invert_562_ == 0)
{
lean_object* v_gate_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_gate_563_ = lean_ctor_get(v_rhs_459_, 0);
lean_inc(v_gate_563_);
v___x_564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_564_, 0, v_gate_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*1, v___x_469_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_561_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___y_536_ = v___x_565_;
goto v___jp_535_;
}
else
{
lean_object* v_gate_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_gate_566_ = lean_ctor_get(v_rhs_459_, 0);
lean_inc(v_gate_566_);
v___x_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_567_, 0, v_gate_566_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*1, v___x_468_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___y_561_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___y_536_ = v___x_568_;
goto v___jp_535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(lean_object* v_aig_573_, lean_object* v_input_574_){
_start:
{
lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v_res_604_; lean_object* v_aig_605_; lean_object* v_ref_606_; lean_object* v___y_608_; lean_object* v_lhs_633_; lean_object* v_rhs_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_673_; 
lean_inc_ref(v_input_574_);
v_res_604_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_573_, v_input_574_);
v_aig_605_ = lean_ctor_get(v_res_604_, 0);
lean_inc_ref(v_aig_605_);
v_ref_606_ = lean_ctor_get(v_res_604_, 1);
lean_inc_ref(v_ref_606_);
lean_dec_ref(v_res_604_);
v_lhs_633_ = lean_ctor_get(v_input_574_, 0);
v_rhs_634_ = lean_ctor_get(v_input_574_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_input_574_);
if (v_isSharedCheck_673_ == 0)
{
v___x_636_ = v_input_574_;
v_isShared_637_ = v_isSharedCheck_673_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_rhs_634_);
lean_inc(v_lhs_633_);
lean_dec(v_input_574_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_673_;
goto v_resetjp_635_;
}
v___jp_575_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_577_);
lean_ctor_set(v___x_579_, 1, v___y_578_);
v___x_580_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v___y_576_, v___x_579_);
return v___x_580_;
}
v___jp_581_:
{
uint8_t v_invert_585_; 
v_invert_585_ = lean_ctor_get_uint8(v___y_582_, sizeof(void*)*1);
if (v_invert_585_ == 0)
{
lean_object* v_gate_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_gate_586_ = lean_ctor_get(v___y_582_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___y_582_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v___y_582_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_gate_586_);
lean_dec(v___y_582_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint8_t v___x_590_; lean_object* v___x_592_; 
v___x_590_ = 1;
if (v_isShared_589_ == 0)
{
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_gate_586_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*1, v___x_590_);
v___y_576_ = v___y_583_;
v___y_577_ = v___y_584_;
v___y_578_ = v___x_592_;
goto v___jp_575_;
}
}
}
else
{
lean_object* v_gate_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
v_gate_595_ = lean_ctor_get(v___y_582_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___y_582_);
if (v_isSharedCheck_603_ == 0)
{
v___x_597_ = v___y_582_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_gate_595_);
lean_dec(v___y_582_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; lean_object* v___x_601_; 
v___x_599_ = 0;
if (v_isShared_598_ == 0)
{
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_gate_595_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*1, v___x_599_);
v___y_576_ = v___y_583_;
v___y_577_ = v___y_584_;
v___y_578_ = v___x_601_;
goto v___jp_575_;
}
}
}
}
v___jp_607_:
{
lean_object* v_res_609_; uint8_t v_invert_610_; 
v_res_609_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_605_, v___y_608_);
v_invert_610_ = lean_ctor_get_uint8(v_ref_606_, sizeof(void*)*1);
if (v_invert_610_ == 0)
{
lean_object* v_aig_611_; lean_object* v_ref_612_; lean_object* v_gate_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
v_aig_611_ = lean_ctor_get(v_res_609_, 0);
lean_inc_ref(v_aig_611_);
v_ref_612_ = lean_ctor_get(v_res_609_, 1);
lean_inc_ref(v_ref_612_);
lean_dec_ref(v_res_609_);
v_gate_613_ = lean_ctor_get(v_ref_606_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_ref_606_);
if (v_isSharedCheck_621_ == 0)
{
v___x_615_ = v_ref_606_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_gate_613_);
lean_dec(v_ref_606_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; lean_object* v___x_619_; 
v___x_617_ = 1;
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
v___y_582_ = v_ref_612_;
v___y_583_ = v_aig_611_;
v___y_584_ = v___x_619_;
goto v___jp_581_;
}
}
}
else
{
lean_object* v_aig_622_; lean_object* v_ref_623_; lean_object* v_gate_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_aig_622_ = lean_ctor_get(v_res_609_, 0);
lean_inc_ref(v_aig_622_);
v_ref_623_ = lean_ctor_get(v_res_609_, 1);
lean_inc_ref(v_ref_623_);
lean_dec_ref(v_res_609_);
v_gate_624_ = lean_ctor_get(v_ref_606_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_ref_606_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v_ref_606_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_gate_624_);
lean_dec(v_ref_606_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; lean_object* v___x_630_; 
v___x_628_ = 0;
if (v_isShared_627_ == 0)
{
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_gate_624_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_628_);
v___y_582_ = v_ref_623_;
v___y_583_ = v_aig_622_;
v___y_584_ = v___x_630_;
goto v___jp_581_;
}
}
}
}
v_resetjp_635_:
{
lean_object* v_gate_638_; uint8_t v_invert_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_672_; 
v_gate_638_ = lean_ctor_get(v_lhs_633_, 0);
v_invert_639_ = lean_ctor_get_uint8(v_lhs_633_, sizeof(void*)*1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_lhs_633_);
if (v_isSharedCheck_672_ == 0)
{
v___x_641_ = v_lhs_633_;
v_isShared_642_ = v_isSharedCheck_672_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_gate_638_);
lean_dec(v_lhs_633_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_672_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_gate_643_; uint8_t v_invert_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_671_; 
v_gate_643_ = lean_ctor_get(v_rhs_634_, 0);
v_invert_644_ = lean_ctor_get_uint8(v_rhs_634_, sizeof(void*)*1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_rhs_634_);
if (v_isSharedCheck_671_ == 0)
{
v___x_646_ = v_rhs_634_;
v_isShared_647_ = v_isSharedCheck_671_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_gate_643_);
lean_dec(v_rhs_634_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_671_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; lean_object* v___y_650_; 
v___x_648_ = 1;
if (v_invert_639_ == 0)
{
lean_object* v___x_665_; 
if (v_isShared_642_ == 0)
{
v___x_665_ = v___x_641_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_gate_638_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*1, v___x_648_);
v___y_650_ = v___x_665_;
goto v___jp_649_;
}
}
else
{
uint8_t v___x_667_; lean_object* v___x_669_; 
v___x_667_ = 0;
if (v_isShared_642_ == 0)
{
v___x_669_ = v___x_641_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_gate_638_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_667_);
v___y_650_ = v___x_669_;
goto v___jp_649_;
}
}
v___jp_649_:
{
if (v_invert_644_ == 0)
{
lean_object* v___x_652_; 
if (v_isShared_647_ == 0)
{
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_gate_643_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*1, v___x_648_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_652_);
lean_ctor_set(v___x_636_, 0, v___y_650_);
v___x_654_ = v___x_636_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___y_650_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v___y_608_ = v___x_654_;
goto v___jp_607_;
}
}
}
else
{
uint8_t v___x_657_; lean_object* v___x_659_; 
v___x_657_ = 0;
if (v_isShared_647_ == 0)
{
v___x_659_ = v___x_646_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_gate_643_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_657_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_659_);
lean_ctor_set(v___x_636_, 0, v___y_650_);
v___x_661_ = v___x_636_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___y_650_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v___y_608_ = v___x_661_;
goto v___jp_607_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object* v_aig_674_, lean_object* v_expr_675_, lean_object* v_cache_676_){
_start:
{
switch(lean_obj_tag(v_expr_675_))
{
case 0:
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_677_ = lean_ctor_get(v_expr_675_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v_expr_675_, 1);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_677_);
lean_ctor_set(v___x_678_, 1, v_cache_676_);
v___x_679_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_674_, v___x_678_);
return v___x_679_;
}
case 1:
{
uint8_t v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_a_680_ = lean_ctor_get_uint8(v_expr_675_, 0);
lean_dec_ref_known(v_expr_675_, 0);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*1, v_a_680_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_aig_674_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_cache_676_);
return v___x_684_;
}
case 2:
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v_result_687_; lean_object* v_ref_688_; uint8_t v_invert_689_; 
v_a_685_ = lean_ctor_get(v_expr_675_, 0);
lean_inc_ref(v_a_685_);
lean_dec_ref_known(v_expr_675_, 1);
v___x_686_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_674_, v_a_685_, v_cache_676_);
v_result_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc_ref(v_result_687_);
v_ref_688_ = lean_ctor_get(v_result_687_, 1);
lean_inc_ref(v_ref_688_);
v_invert_689_ = lean_ctor_get_uint8(v_ref_688_, sizeof(void*)*1);
if (v_invert_689_ == 0)
{
lean_object* v_cache_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_715_; 
v_cache_690_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_686_, 0);
lean_dec(v_unused_716_);
v___x_692_ = v___x_686_;
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_cache_690_);
lean_dec(v___x_686_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_aig_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_713_; 
v_aig_694_ = lean_ctor_get(v_result_687_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_result_687_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v_result_687_, 1);
lean_dec(v_unused_714_);
v___x_696_ = v_result_687_;
v_isShared_697_ = v_isSharedCheck_713_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_aig_694_);
lean_dec(v_result_687_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_713_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_gate_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_712_; 
v_gate_698_ = lean_ctor_get(v_ref_688_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_ref_688_);
if (v_isSharedCheck_712_ == 0)
{
v___x_700_ = v_ref_688_;
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_gate_698_);
lean_dec(v_ref_688_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_712_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; lean_object* v___x_704_; 
v___x_702_ = 1;
if (v_isShared_701_ == 0)
{
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_gate_698_);
v___x_704_ = v_reuseFailAlloc_711_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*1, v___x_702_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_aig_694_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_706_);
v___x_708_ = v___x_692_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_cache_690_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
}
else
{
lean_object* v_cache_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_742_; 
v_cache_717_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_686_, 0);
lean_dec(v_unused_743_);
v___x_719_ = v___x_686_;
v_isShared_720_ = v_isSharedCheck_742_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_cache_717_);
lean_dec(v___x_686_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_742_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_aig_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_740_; 
v_aig_721_ = lean_ctor_get(v_result_687_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_result_687_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_result_687_, 1);
lean_dec(v_unused_741_);
v___x_723_ = v_result_687_;
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_aig_721_);
lean_dec(v_result_687_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_gate_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_739_; 
v_gate_725_ = lean_ctor_get(v_ref_688_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_ref_688_);
if (v_isSharedCheck_739_ == 0)
{
v___x_727_ = v_ref_688_;
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_gate_725_);
lean_dec(v_ref_688_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint8_t v___x_729_; lean_object* v___x_731_; 
v___x_729_ = 0;
if (v_isShared_728_ == 0)
{
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_gate_725_);
v___x_731_ = v_reuseFailAlloc_738_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_729_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_731_);
v___x_733_ = v___x_723_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_aig_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_733_);
v___x_735_ = v___x_719_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_cache_717_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
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
uint8_t v_a_744_; lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v_result_748_; lean_object* v_cache_749_; lean_object* v_aig_750_; lean_object* v_ref_751_; lean_object* v___x_752_; lean_object* v_result_753_; lean_object* v_cache_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_792_; 
v_a_744_ = lean_ctor_get_uint8(v_expr_675_, sizeof(void*)*2);
v_a_745_ = lean_ctor_get(v_expr_675_, 0);
lean_inc_ref(v_a_745_);
v_a_746_ = lean_ctor_get(v_expr_675_, 1);
lean_inc_ref(v_a_746_);
lean_dec_ref_known(v_expr_675_, 2);
v___x_747_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_674_, v_a_745_, v_cache_676_);
v_result_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_ref(v_result_748_);
v_cache_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc_ref(v_cache_749_);
lean_dec_ref(v___x_747_);
v_aig_750_ = lean_ctor_get(v_result_748_, 0);
lean_inc_ref(v_aig_750_);
v_ref_751_ = lean_ctor_get(v_result_748_, 1);
lean_inc_ref(v_ref_751_);
lean_dec_ref(v_result_748_);
v___x_752_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_750_, v_a_746_, v_cache_749_);
v_result_753_ = lean_ctor_get(v___x_752_, 0);
v_cache_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_792_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_792_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_cache_754_);
lean_inc(v_result_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_792_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_aig_758_; lean_object* v_ref_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_791_; 
v_aig_758_ = lean_ctor_get(v_result_753_, 0);
v_ref_759_ = lean_ctor_get(v_result_753_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_result_753_);
if (v_isSharedCheck_791_ == 0)
{
v___x_761_ = v_result_753_;
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_ref_759_);
lean_inc(v_aig_758_);
lean_dec(v_result_753_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_gate_763_; uint8_t v_invert_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_790_; 
v_gate_763_ = lean_ctor_get(v_ref_751_, 0);
v_invert_764_ = lean_ctor_get_uint8(v_ref_751_, sizeof(void*)*1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_ref_751_);
if (v_isSharedCheck_790_ == 0)
{
v___x_766_ = v_ref_751_;
v_isShared_767_ = v_isSharedCheck_790_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_gate_763_);
lean_dec(v_ref_751_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_790_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_lhsRef_769_; 
if (v_isShared_767_ == 0)
{
v_lhsRef_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_gate_763_);
lean_ctor_set_uint8(v_reuseFailAlloc_789_, sizeof(void*)*1, v_invert_764_);
v_lhsRef_769_ = v_reuseFailAlloc_789_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v_input_771_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_lhsRef_769_);
v_input_771_ = v___x_761_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_lhsRef_769_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_ref_759_);
v_input_771_ = v_reuseFailAlloc_788_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
switch(v_a_744_)
{
case 0:
{
lean_object* v_ret_772_; lean_object* v___x_774_; 
v_ret_772_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0(v_aig_758_, v_input_771_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_ret_772_);
v___x_774_ = v___x_756_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_ret_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_cache_754_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
case 1:
{
lean_object* v_ret_776_; lean_object* v___x_778_; 
v_ret_776_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__1(v_aig_758_, v_input_771_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_ret_776_);
v___x_778_ = v___x_756_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_ret_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_cache_754_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
case 2:
{
lean_object* v_ret_780_; lean_object* v___x_782_; 
v_ret_780_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__2(v_aig_758_, v_input_771_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_ret_780_);
v___x_782_ = v___x_756_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_ret_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_cache_754_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
default: 
{
lean_object* v_ret_784_; lean_object* v___x_786_; 
v_ret_784_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_758_, v_input_771_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_ret_784_);
v___x_786_ = v___x_756_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_ret_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_cache_754_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
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
lean_object* v_a_793_; lean_object* v_a_794_; lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_843_; 
v_a_793_ = lean_ctor_get(v_expr_675_, 0);
v_a_794_ = lean_ctor_get(v_expr_675_, 1);
v_a_795_ = lean_ctor_get(v_expr_675_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_expr_675_);
if (v_isSharedCheck_843_ == 0)
{
v___x_797_ = v_expr_675_;
v_isShared_798_ = v_isSharedCheck_843_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_inc(v_a_794_);
lean_inc(v_a_793_);
lean_dec(v_expr_675_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_843_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v_result_800_; lean_object* v_cache_801_; lean_object* v_aig_802_; lean_object* v_ref_803_; lean_object* v___x_804_; lean_object* v_result_805_; lean_object* v_cache_806_; lean_object* v_aig_807_; lean_object* v_ref_808_; lean_object* v___x_809_; lean_object* v_result_810_; lean_object* v_cache_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_842_; 
v___x_799_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_674_, v_a_793_, v_cache_676_);
v_result_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc_ref(v_result_800_);
v_cache_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc_ref(v_cache_801_);
lean_dec_ref(v___x_799_);
v_aig_802_ = lean_ctor_get(v_result_800_, 0);
lean_inc_ref(v_aig_802_);
v_ref_803_ = lean_ctor_get(v_result_800_, 1);
lean_inc_ref(v_ref_803_);
lean_dec_ref(v_result_800_);
v___x_804_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_802_, v_a_794_, v_cache_801_);
v_result_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_result_805_);
v_cache_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc_ref(v_cache_806_);
lean_dec_ref(v___x_804_);
v_aig_807_ = lean_ctor_get(v_result_805_, 0);
lean_inc_ref(v_aig_807_);
v_ref_808_ = lean_ctor_get(v_result_805_, 1);
lean_inc_ref(v_ref_808_);
lean_dec_ref(v_result_805_);
v___x_809_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_807_, v_a_795_, v_cache_806_);
v_result_810_ = lean_ctor_get(v___x_809_, 0);
v_cache_811_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_842_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_cache_811_);
lean_inc(v_result_810_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_aig_815_; lean_object* v_ref_816_; lean_object* v_gate_817_; uint8_t v_invert_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_841_; 
v_aig_815_ = lean_ctor_get(v_result_810_, 0);
lean_inc_ref(v_aig_815_);
v_ref_816_ = lean_ctor_get(v_result_810_, 1);
lean_inc_ref(v_ref_816_);
lean_dec_ref(v_result_810_);
v_gate_817_ = lean_ctor_get(v_ref_803_, 0);
v_invert_818_ = lean_ctor_get_uint8(v_ref_803_, sizeof(void*)*1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_ref_803_);
if (v_isSharedCheck_841_ == 0)
{
v___x_820_ = v_ref_803_;
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_gate_817_);
lean_dec(v_ref_803_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_gate_822_; uint8_t v_invert_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_840_; 
v_gate_822_ = lean_ctor_get(v_ref_808_, 0);
v_invert_823_ = lean_ctor_get_uint8(v_ref_808_, sizeof(void*)*1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_ref_808_);
if (v_isSharedCheck_840_ == 0)
{
v___x_825_ = v_ref_808_;
v_isShared_826_ = v_isSharedCheck_840_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_gate_822_);
lean_dec(v_ref_808_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_840_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_discrRef_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_gate_817_);
v_discrRef_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_gate_817_);
v_discrRef_828_ = v_reuseFailAlloc_839_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v_lhsRef_830_; 
lean_ctor_set_uint8(v_discrRef_828_, sizeof(void*)*1, v_invert_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_gate_822_);
v_lhsRef_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_gate_822_);
v_lhsRef_830_ = v_reuseFailAlloc_838_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v_input_832_; 
lean_ctor_set_uint8(v_lhsRef_830_, sizeof(void*)*1, v_invert_823_);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 0);
lean_ctor_set(v___x_797_, 2, v_ref_816_);
lean_ctor_set(v___x_797_, 1, v_lhsRef_830_);
lean_ctor_set(v___x_797_, 0, v_discrRef_828_);
v_input_832_ = v___x_797_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_discrRef_828_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_lhsRef_830_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_ref_816_);
v_input_832_ = v_reuseFailAlloc_837_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v_ret_833_; lean_object* v___x_835_; 
v_ret_833_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(v_aig_815_, v_input_832_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_ret_833_);
v___x_835_ = v___x_813_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_ret_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_cache_811_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___redArg(v_m_845_, v_a_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_848_, lean_object* v_m_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1(v_00_u03b2_848_, v_m_849_, v_a_850_);
lean_dec_ref(v_m_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_852_, lean_object* v_m_853_, lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3___redArg(v_m_853_, v_a_854_, v_b_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_857_, lean_object* v_a_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__1_spec__7___redArg(v_a_858_, v_x_859_);
return v___x_860_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_861_, lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___redArg(v_a_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_862_ = stack[1].m_obj;
lean_object* v_x_863_ = stack[2].m_obj;
uint8_t v_res_865_;
v_res_865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(lean_box(0), v_a_862_, v_x_863_);
stack->m_num = v_res_865_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_866_, lean_object* v_a_867_, lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_866_, v_a_867_, v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_871_, lean_object* v_data_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11___redArg(v_data_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_874_, lean_object* v_a_875_, lean_object* v_b_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__12___redArg(v_a_875_, v_b_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_879_, lean_object* v_i_880_, lean_object* v_source_881_, lean_object* v_target_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(v_i_880_, v_source_881_, v_target_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object* v_expr_888_, lean_object* v_aig_889_, lean_object* v_cache_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_889_, v_expr_888_, v_cache_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_unsigned_to_nat(16u);
v___x_898_ = lean_mk_array(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_903_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_905_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_unsigned_to_nat(16u);
v___x_908_ = lean_mk_array(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_result_916_; 
v___x_913_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_914_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
v___x_915_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v___x_913_, v_expr_912_, v___x_914_);
v_result_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_result_916_);
lean_dec_ref(v___x_915_);
return v_result_916_;
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
