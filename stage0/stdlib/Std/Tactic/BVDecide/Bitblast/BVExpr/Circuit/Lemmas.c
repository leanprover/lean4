// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred import Init.ByCases import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter___redArg(lean_object* v_cache_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v_exprs_3_; lean_object* v_map_4_; lean_object* v___x_5_; 
v_exprs_3_ = lean_ctor_get(v_cache_1_, 0);
lean_inc_ref(v_exprs_3_);
v_map_4_ = lean_ctor_get(v_cache_1_, 1);
lean_inc_ref(v_map_4_);
lean_dec_ref(v_cache_1_);
v___x_5_ = lean_apply_3(v_h__1_2_, v_exprs_3_, v_map_4_, lean_box(0));
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter(lean_object* v_aig_6_, lean_object* v_motive_7_, lean_object* v_cache_8_, lean_object* v_h__1_9_){
_start:
{
lean_object* v_exprs_10_; lean_object* v_map_11_; lean_object* v___x_12_; 
v_exprs_10_ = lean_ctor_get(v_cache_8_, 0);
lean_inc_ref(v_exprs_10_);
v_map_11_ = lean_ctor_get(v_cache_8_, 1);
lean_inc_ref(v_map_11_);
lean_dec_ref(v_cache_8_);
v___x_12_ = lean_apply_3(v_h__1_9_, v_exprs_10_, v_map_11_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter___boxed(lean_object* v_aig_13_, lean_object* v_motive_14_, lean_object* v_cache_15_, lean_object* v_h__1_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert_match__1_splitter(v_aig_13_, v_motive_14_, v_cache_15_, v_h__1_16_);
lean_dec_ref(v_aig_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_21_; 
lean_dec(v_h__1_19_);
v___x_21_ = lean_apply_1(v_h__2_20_, lean_box(0));
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v_val_22_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v_x_18_, 1);
v___x_23_ = lean_apply_2(v_h__1_19_, v_val_22_, lean_box(0));
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter(lean_object* v_motive_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_h__1_26_);
v___x_28_ = lean_apply_1(v_h__2_27_, lean_box(0));
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_27_);
v_val_29_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_29_);
lean_dec_ref_known(v_x_25_, 1);
v___x_30_ = lean_apply_2(v_h__1_26_, v_val_29_, lean_box(0));
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_32_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__2_33_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_33_);
v_val_36_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v_x_31_, 1);
v___x_37_ = lean_apply_1(v_h__1_32_, v_val_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object* v_aig_38_, lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_41_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__2_42_, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_42_);
v_val_45_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v_x_40_, 1);
v___x_46_ = lean_apply_1(v_h__1_41_, v_val_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object* v_aig_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(v_aig_47_, v_motive_48_, v_x_49_, v_h__1_50_, v_h__2_51_);
lean_dec_ref(v_aig_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object* v_expr_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_, lean_object* v_h__4_57_, lean_object* v_h__5_58_){
_start:
{
switch(lean_obj_tag(v_expr_53_))
{
case 0:
{
lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_h__5_58_);
lean_dec(v_h__4_57_);
lean_dec(v_h__3_56_);
lean_dec(v_h__2_55_);
v_a_59_ = lean_ctor_get(v_expr_53_, 0);
lean_inc_ref(v_a_59_);
lean_dec_ref_known(v_expr_53_, 1);
v___x_60_ = lean_apply_1(v_h__1_54_, v_a_59_);
return v___x_60_;
}
case 1:
{
uint8_t v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__5_58_);
lean_dec(v_h__4_57_);
lean_dec(v_h__3_56_);
lean_dec(v_h__1_54_);
v_a_61_ = lean_ctor_get_uint8(v_expr_53_, 8);
lean_dec_ref_known(v_expr_53_, 0);
v___x_62_ = lean_box(v_a_61_);
v___x_63_ = lean_apply_1(v_h__2_55_, v___x_62_);
return v___x_63_;
}
case 2:
{
lean_object* v_a_64_; lean_object* v___x_65_; 
lean_dec(v_h__5_58_);
lean_dec(v_h__4_57_);
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v_a_64_ = lean_ctor_get(v_expr_53_, 0);
lean_inc_ref(v_a_64_);
lean_dec_ref_known(v_expr_53_, 1);
v___x_65_ = lean_apply_1(v_h__3_56_, v_a_64_);
return v___x_65_;
}
case 3:
{
uint8_t v_a_66_; lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__4_57_);
lean_dec(v_h__3_56_);
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v_a_66_ = lean_ctor_get_uint8(v_expr_53_, sizeof(void*)*2 + 8);
v_a_67_ = lean_ctor_get(v_expr_53_, 0);
lean_inc_ref(v_a_67_);
v_a_68_ = lean_ctor_get(v_expr_53_, 1);
lean_inc_ref(v_a_68_);
lean_dec_ref_known(v_expr_53_, 2);
v___x_69_ = lean_box(v_a_66_);
v___x_70_ = lean_apply_3(v_h__5_58_, v___x_69_, v_a_67_, v_a_68_);
return v___x_70_;
}
default: 
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_h__5_58_);
lean_dec(v_h__3_56_);
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v_a_71_ = lean_ctor_get(v_expr_53_, 0);
lean_inc_ref(v_a_71_);
v_a_72_ = lean_ctor_get(v_expr_53_, 1);
lean_inc_ref(v_a_72_);
v_a_73_ = lean_ctor_get(v_expr_53_, 2);
lean_inc_ref(v_a_73_);
lean_dec_ref_known(v_expr_53_, 3);
v___x_74_ = lean_apply_3(v_h__4_57_, v_a_71_, v_a_72_, v_a_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object* v_motive_75_, lean_object* v_expr_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_, lean_object* v_h__3_79_, lean_object* v_h__4_80_, lean_object* v_h__5_81_){
_start:
{
switch(lean_obj_tag(v_expr_76_))
{
case 0:
{
lean_object* v_a_82_; lean_object* v___x_83_; 
lean_dec(v_h__5_81_);
lean_dec(v_h__4_80_);
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
v_a_82_ = lean_ctor_get(v_expr_76_, 0);
lean_inc_ref(v_a_82_);
lean_dec_ref_known(v_expr_76_, 1);
v___x_83_ = lean_apply_1(v_h__1_77_, v_a_82_);
return v___x_83_;
}
case 1:
{
uint8_t v_a_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_h__5_81_);
lean_dec(v_h__4_80_);
lean_dec(v_h__3_79_);
lean_dec(v_h__1_77_);
v_a_84_ = lean_ctor_get_uint8(v_expr_76_, 8);
lean_dec_ref_known(v_expr_76_, 0);
v___x_85_ = lean_box(v_a_84_);
v___x_86_ = lean_apply_1(v_h__2_78_, v___x_85_);
return v___x_86_;
}
case 2:
{
lean_object* v_a_87_; lean_object* v___x_88_; 
lean_dec(v_h__5_81_);
lean_dec(v_h__4_80_);
lean_dec(v_h__2_78_);
lean_dec(v_h__1_77_);
v_a_87_ = lean_ctor_get(v_expr_76_, 0);
lean_inc_ref(v_a_87_);
lean_dec_ref_known(v_expr_76_, 1);
v___x_88_ = lean_apply_1(v_h__3_79_, v_a_87_);
return v___x_88_;
}
case 3:
{
uint8_t v_a_89_; lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__4_80_);
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
lean_dec(v_h__1_77_);
v_a_89_ = lean_ctor_get_uint8(v_expr_76_, sizeof(void*)*2 + 8);
v_a_90_ = lean_ctor_get(v_expr_76_, 0);
lean_inc_ref(v_a_90_);
v_a_91_ = lean_ctor_get(v_expr_76_, 1);
lean_inc_ref(v_a_91_);
lean_dec_ref_known(v_expr_76_, 2);
v___x_92_ = lean_box(v_a_89_);
v___x_93_ = lean_apply_3(v_h__5_81_, v___x_92_, v_a_90_, v_a_91_);
return v___x_93_;
}
default: 
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; 
lean_dec(v_h__5_81_);
lean_dec(v_h__3_79_);
lean_dec(v_h__2_78_);
lean_dec(v_h__1_77_);
v_a_94_ = lean_ctor_get(v_expr_76_, 0);
lean_inc_ref(v_a_94_);
v_a_95_ = lean_ctor_get(v_expr_76_, 1);
lean_inc_ref(v_a_95_);
v_a_96_ = lean_ctor_get(v_expr_76_, 2);
lean_inc_ref(v_a_96_);
lean_dec_ref_known(v_expr_76_, 3);
v___x_97_ = lean_apply_3(v_h__4_80_, v_a_94_, v_a_95_, v_a_96_);
return v___x_97_;
}
}
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
