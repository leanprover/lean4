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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref_known(v_x_1_, 1);
v___x_6_ = lean_apply_2(v_h__1_2_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f_match__1_splitter(lean_object* v_motive_7_, lean_object* v_x_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v___x_11_; 
lean_dec(v_h__1_9_);
v___x_11_ = lean_apply_1(v_h__2_10_, lean_box(0));
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v___x_13_; 
lean_dec(v_h__2_10_);
v_val_12_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v_x_8_, 1);
v___x_13_ = lean_apply_2(v_h__1_9_, v_val_12_, lean_box(0));
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v_val_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_19_);
lean_dec_ref_known(v_x_14_, 1);
v___x_20_ = lean_apply_1(v_h__1_15_, v_val_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object* v_aig_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_24_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__2_25_, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; 
lean_dec(v_h__2_25_);
v_val_28_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_x_23_, 1);
v___x_29_ = lean_apply_1(v_h__1_24_, v_val_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object* v_aig_30_, lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(v_aig_30_, v_motive_31_, v_x_32_, v_h__1_33_, v_h__2_34_);
lean_dec_ref(v_aig_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object* v_expr_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_, lean_object* v_h__3_39_, lean_object* v_h__4_40_, lean_object* v_h__5_41_){
_start:
{
switch(lean_obj_tag(v_expr_36_))
{
case 0:
{
lean_object* v_a_42_; lean_object* v___x_43_; 
lean_dec(v_h__5_41_);
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
lean_dec(v_h__2_38_);
v_a_42_ = lean_ctor_get(v_expr_36_, 0);
lean_inc_ref(v_a_42_);
lean_dec_ref_known(v_expr_36_, 1);
v___x_43_ = lean_apply_1(v_h__1_37_, v_a_42_);
return v___x_43_;
}
case 1:
{
uint8_t v_a_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__5_41_);
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
lean_dec(v_h__1_37_);
v_a_44_ = lean_ctor_get_uint8(v_expr_36_, 8);
lean_dec_ref_known(v_expr_36_, 0);
v___x_45_ = lean_box(v_a_44_);
v___x_46_ = lean_apply_1(v_h__2_38_, v___x_45_);
return v___x_46_;
}
case 2:
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__5_41_);
lean_dec(v_h__4_40_);
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
v_a_47_ = lean_ctor_get(v_expr_36_, 0);
lean_inc_ref(v_a_47_);
lean_dec_ref_known(v_expr_36_, 1);
v___x_48_ = lean_apply_1(v_h__3_39_, v_a_47_);
return v___x_48_;
}
case 3:
{
uint8_t v_a_49_; lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
v_a_49_ = lean_ctor_get_uint8(v_expr_36_, sizeof(void*)*2 + 8);
v_a_50_ = lean_ctor_get(v_expr_36_, 0);
lean_inc_ref(v_a_50_);
v_a_51_ = lean_ctor_get(v_expr_36_, 1);
lean_inc_ref(v_a_51_);
lean_dec_ref_known(v_expr_36_, 2);
v___x_52_ = lean_box(v_a_49_);
v___x_53_ = lean_apply_3(v_h__5_41_, v___x_52_, v_a_50_, v_a_51_);
return v___x_53_;
}
default: 
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_h__5_41_);
lean_dec(v_h__3_39_);
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
v_a_54_ = lean_ctor_get(v_expr_36_, 0);
lean_inc_ref(v_a_54_);
v_a_55_ = lean_ctor_get(v_expr_36_, 1);
lean_inc_ref(v_a_55_);
v_a_56_ = lean_ctor_get(v_expr_36_, 2);
lean_inc_ref(v_a_56_);
lean_dec_ref_known(v_expr_36_, 3);
v___x_57_ = lean_apply_3(v_h__4_40_, v_a_54_, v_a_55_, v_a_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object* v_motive_58_, lean_object* v_expr_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_, lean_object* v_h__4_63_, lean_object* v_h__5_64_){
_start:
{
switch(lean_obj_tag(v_expr_59_))
{
case 0:
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__5_64_);
lean_dec(v_h__4_63_);
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
v_a_65_ = lean_ctor_get(v_expr_59_, 0);
lean_inc_ref(v_a_65_);
lean_dec_ref_known(v_expr_59_, 1);
v___x_66_ = lean_apply_1(v_h__1_60_, v_a_65_);
return v___x_66_;
}
case 1:
{
uint8_t v_a_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_h__5_64_);
lean_dec(v_h__4_63_);
lean_dec(v_h__3_62_);
lean_dec(v_h__1_60_);
v_a_67_ = lean_ctor_get_uint8(v_expr_59_, 8);
lean_dec_ref_known(v_expr_59_, 0);
v___x_68_ = lean_box(v_a_67_);
v___x_69_ = lean_apply_1(v_h__2_61_, v___x_68_);
return v___x_69_;
}
case 2:
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__5_64_);
lean_dec(v_h__4_63_);
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v_a_70_ = lean_ctor_get(v_expr_59_, 0);
lean_inc_ref(v_a_70_);
lean_dec_ref_known(v_expr_59_, 1);
v___x_71_ = lean_apply_1(v_h__3_62_, v_a_70_);
return v___x_71_;
}
case 3:
{
uint8_t v_a_72_; lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__4_63_);
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v_a_72_ = lean_ctor_get_uint8(v_expr_59_, sizeof(void*)*2 + 8);
v_a_73_ = lean_ctor_get(v_expr_59_, 0);
lean_inc_ref(v_a_73_);
v_a_74_ = lean_ctor_get(v_expr_59_, 1);
lean_inc_ref(v_a_74_);
lean_dec_ref_known(v_expr_59_, 2);
v___x_75_ = lean_box(v_a_72_);
v___x_76_ = lean_apply_3(v_h__5_64_, v___x_75_, v_a_73_, v_a_74_);
return v___x_76_;
}
default: 
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_h__5_64_);
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v_a_77_ = lean_ctor_get(v_expr_59_, 0);
lean_inc_ref(v_a_77_);
v_a_78_ = lean_ctor_get(v_expr_59_, 1);
lean_inc_ref(v_a_78_);
v_a_79_ = lean_ctor_get(v_expr_59_, 2);
lean_inc_ref(v_a_79_);
lean_dec_ref_known(v_expr_59_, 3);
v___x_80_ = lean_apply_3(v_h__4_63_, v_a_77_, v_a_78_, v_a_79_);
return v___x_80_;
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
