// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr import Init.ByCases import Init.Data.Nat.Internal.Linear import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter___redArg(lean_object* v_cache_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_h__1_2_, v_cache_1_, lean_box(0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter(lean_object* v_aig_4_, lean_object* v_motive_5_, lean_object* v_cache_6_, lean_object* v_h__1_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_h__1_7_, v_cache_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter___boxed(lean_object* v_aig_9_, lean_object* v_motive_10_, lean_object* v_cache_11_, lean_object* v_h__1_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_insert_match__1_splitter(v_aig_9_, v_motive_10_, v_cache_11_, v_h__1_12_);
lean_dec_ref(v_aig_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_17_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_apply_1(v_h__2_16_, lean_box(0));
return v___x_17_;
}
else
{
lean_object* v_val_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_16_);
v_val_18_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_18_);
lean_dec_ref_known(v_x_14_, 1);
v___x_19_ = lean_apply_2(v_h__1_15_, v_val_18_, lean_box(0));
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(lean_object* v_w_20_, lean_object* v_expr_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_26_; 
lean_dec(v_h__1_24_);
v___x_26_ = lean_apply_1(v_h__2_25_, lean_box(0));
return v___x_26_;
}
else
{
lean_object* v_val_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_25_);
v_val_27_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_val_27_);
lean_dec_ref_known(v_x_23_, 1);
v___x_28_ = lean_apply_2(v_h__1_24_, v_val_27_, lean_box(0));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(lean_object* v_w_29_, lean_object* v_expr_30_, lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_29_, v_expr_30_, v_motive_31_, v_x_32_, v_h__1_33_, v_h__2_34_);
lean_dec_ref(v_expr_30_);
lean_dec(v_w_29_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__2_38_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_val_41_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v_x_36_, 1);
v___x_42_ = lean_apply_1(v_h__1_37_, v_val_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(lean_object* v_w_43_, lean_object* v_aig_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_47_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__2_48_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_48_);
v_val_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_x_46_, 1);
v___x_52_ = lean_apply_1(v_h__1_47_, v_val_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(lean_object* v_w_53_, lean_object* v_aig_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_53_, v_aig_54_, v_motive_55_, v_x_56_, v_h__1_57_, v_h__2_58_);
lean_dec_ref(v_aig_54_);
lean_dec(v_w_53_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(lean_object* v_w_60_, lean_object* v_expr_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_, lean_object* v_h__4_65_, lean_object* v_h__5_66_, lean_object* v_h__6_67_, lean_object* v_h__7_68_, lean_object* v_h__8_69_, lean_object* v_h__9_70_, lean_object* v_h__10_71_){
_start:
{
switch(lean_obj_tag(v_expr_61_))
{
case 0:
{
lean_object* v_idx_72_; lean_object* v___x_73_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
v_idx_72_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_idx_72_);
lean_dec_ref_known(v_expr_61_, 2);
v___x_73_ = lean_apply_2(v_h__1_62_, v_w_60_, v_idx_72_);
return v___x_73_;
}
case 1:
{
lean_object* v_val_74_; lean_object* v___x_75_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__1_62_);
v_val_74_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_val_74_);
lean_dec_ref_known(v_expr_61_, 2);
v___x_75_ = lean_apply_2(v_h__2_63_, v_w_60_, v_val_74_);
return v___x_75_;
}
case 2:
{
lean_object* v_w_76_; lean_object* v_start_77_; lean_object* v_expr_78_; lean_object* v___x_79_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_w_76_ = lean_ctor_get(v_expr_61_, 0);
lean_inc(v_w_76_);
v_start_77_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_start_77_);
v_expr_78_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_expr_78_);
lean_dec_ref_known(v_expr_61_, 4);
v___x_79_ = lean_apply_4(v_h__7_68_, v_w_60_, v_w_76_, v_start_77_, v_expr_78_);
return v___x_79_;
}
case 3:
{
lean_object* v_lhs_80_; uint8_t v_op_81_; lean_object* v_rhs_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_lhs_80_ = lean_ctor_get(v_expr_61_, 1);
lean_inc_ref(v_lhs_80_);
v_op_81_ = lean_ctor_get_uint8(v_expr_61_, sizeof(void*)*3 + 8);
v_rhs_82_ = lean_ctor_get(v_expr_61_, 2);
lean_inc_ref(v_rhs_82_);
lean_dec_ref_known(v_expr_61_, 3);
v___x_83_ = lean_box(v_op_81_);
v___x_84_ = lean_apply_4(v_h__3_64_, v_w_60_, v_lhs_80_, v___x_83_, v_rhs_82_);
return v___x_84_;
}
case 4:
{
lean_object* v_op_85_; lean_object* v_operand_86_; lean_object* v___x_87_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_op_85_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_op_85_);
v_operand_86_ = lean_ctor_get(v_expr_61_, 2);
lean_inc_ref(v_operand_86_);
lean_dec_ref_known(v_expr_61_, 3);
v___x_87_ = lean_apply_3(v_h__4_65_, v_w_60_, v_op_85_, v_operand_86_);
return v___x_87_;
}
case 5:
{
lean_object* v_l_88_; lean_object* v_r_89_; lean_object* v_lhs_90_; lean_object* v_rhs_91_; lean_object* v___x_92_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_l_88_ = lean_ctor_get(v_expr_61_, 0);
lean_inc(v_l_88_);
v_r_89_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_r_89_);
v_lhs_90_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_lhs_90_);
v_rhs_91_ = lean_ctor_get(v_expr_61_, 4);
lean_inc_ref(v_rhs_91_);
lean_dec_ref_known(v_expr_61_, 5);
v___x_92_ = lean_apply_6(v_h__5_66_, v_w_60_, v_l_88_, v_r_89_, v_lhs_90_, v_rhs_91_, lean_box(0));
return v___x_92_;
}
case 6:
{
lean_object* v_w_93_; lean_object* v_n_94_; lean_object* v_expr_95_; lean_object* v___x_96_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_w_93_ = lean_ctor_get(v_expr_61_, 0);
lean_inc(v_w_93_);
v_n_94_ = lean_ctor_get(v_expr_61_, 2);
lean_inc(v_n_94_);
v_expr_95_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_expr_95_);
lean_dec_ref_known(v_expr_61_, 4);
v___x_96_ = lean_apply_5(v_h__6_67_, v_w_60_, v_w_93_, v_n_94_, v_expr_95_, lean_box(0));
return v___x_96_;
}
case 7:
{
lean_object* v_n_97_; lean_object* v_lhs_98_; lean_object* v_rhs_99_; lean_object* v___x_100_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__9_70_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_n_97_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_n_97_);
v_lhs_98_ = lean_ctor_get(v_expr_61_, 2);
lean_inc_ref(v_lhs_98_);
v_rhs_99_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_rhs_99_);
lean_dec_ref_known(v_expr_61_, 4);
v___x_100_ = lean_apply_4(v_h__8_69_, v_w_60_, v_n_97_, v_lhs_98_, v_rhs_99_);
return v___x_100_;
}
case 8:
{
lean_object* v_n_101_; lean_object* v_lhs_102_; lean_object* v_rhs_103_; lean_object* v___x_104_; 
lean_dec(v_h__10_71_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_n_101_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_n_101_);
v_lhs_102_ = lean_ctor_get(v_expr_61_, 2);
lean_inc_ref(v_lhs_102_);
v_rhs_103_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_rhs_103_);
lean_dec_ref_known(v_expr_61_, 4);
v___x_104_ = lean_apply_4(v_h__9_70_, v_w_60_, v_n_101_, v_lhs_102_, v_rhs_103_);
return v___x_104_;
}
default: 
{
lean_object* v_n_105_; lean_object* v_lhs_106_; lean_object* v_rhs_107_; lean_object* v___x_108_; 
lean_dec(v_h__9_70_);
lean_dec(v_h__8_69_);
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_n_105_ = lean_ctor_get(v_expr_61_, 1);
lean_inc(v_n_105_);
v_lhs_106_ = lean_ctor_get(v_expr_61_, 2);
lean_inc_ref(v_lhs_106_);
v_rhs_107_ = lean_ctor_get(v_expr_61_, 3);
lean_inc_ref(v_rhs_107_);
lean_dec_ref_known(v_expr_61_, 4);
v___x_108_ = lean_apply_4(v_h__10_71_, v_w_60_, v_n_105_, v_lhs_106_, v_rhs_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(lean_object* v_motive_109_, lean_object* v_w_110_, lean_object* v_expr_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_, lean_object* v_h__4_115_, lean_object* v_h__5_116_, lean_object* v_h__6_117_, lean_object* v_h__7_118_, lean_object* v_h__8_119_, lean_object* v_h__9_120_, lean_object* v_h__10_121_){
_start:
{
switch(lean_obj_tag(v_expr_111_))
{
case 0:
{
lean_object* v_idx_122_; lean_object* v___x_123_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
v_idx_122_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_idx_122_);
lean_dec_ref_known(v_expr_111_, 2);
v___x_123_ = lean_apply_2(v_h__1_112_, v_w_110_, v_idx_122_);
return v___x_123_;
}
case 1:
{
lean_object* v_val_124_; lean_object* v___x_125_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__1_112_);
v_val_124_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_val_124_);
lean_dec_ref_known(v_expr_111_, 2);
v___x_125_ = lean_apply_2(v_h__2_113_, v_w_110_, v_val_124_);
return v___x_125_;
}
case 2:
{
lean_object* v_w_126_; lean_object* v_start_127_; lean_object* v_expr_128_; lean_object* v___x_129_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_w_126_ = lean_ctor_get(v_expr_111_, 0);
lean_inc(v_w_126_);
v_start_127_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_start_127_);
v_expr_128_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_expr_128_);
lean_dec_ref_known(v_expr_111_, 4);
v___x_129_ = lean_apply_4(v_h__7_118_, v_w_110_, v_w_126_, v_start_127_, v_expr_128_);
return v___x_129_;
}
case 3:
{
lean_object* v_lhs_130_; uint8_t v_op_131_; lean_object* v_rhs_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_lhs_130_ = lean_ctor_get(v_expr_111_, 1);
lean_inc_ref(v_lhs_130_);
v_op_131_ = lean_ctor_get_uint8(v_expr_111_, sizeof(void*)*3 + 8);
v_rhs_132_ = lean_ctor_get(v_expr_111_, 2);
lean_inc_ref(v_rhs_132_);
lean_dec_ref_known(v_expr_111_, 3);
v___x_133_ = lean_box(v_op_131_);
v___x_134_ = lean_apply_4(v_h__3_114_, v_w_110_, v_lhs_130_, v___x_133_, v_rhs_132_);
return v___x_134_;
}
case 4:
{
lean_object* v_op_135_; lean_object* v_operand_136_; lean_object* v___x_137_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_op_135_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_op_135_);
v_operand_136_ = lean_ctor_get(v_expr_111_, 2);
lean_inc_ref(v_operand_136_);
lean_dec_ref_known(v_expr_111_, 3);
v___x_137_ = lean_apply_3(v_h__4_115_, v_w_110_, v_op_135_, v_operand_136_);
return v___x_137_;
}
case 5:
{
lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v_lhs_140_; lean_object* v_rhs_141_; lean_object* v___x_142_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_l_138_ = lean_ctor_get(v_expr_111_, 0);
lean_inc(v_l_138_);
v_r_139_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_r_139_);
v_lhs_140_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_lhs_140_);
v_rhs_141_ = lean_ctor_get(v_expr_111_, 4);
lean_inc_ref(v_rhs_141_);
lean_dec_ref_known(v_expr_111_, 5);
v___x_142_ = lean_apply_6(v_h__5_116_, v_w_110_, v_l_138_, v_r_139_, v_lhs_140_, v_rhs_141_, lean_box(0));
return v___x_142_;
}
case 6:
{
lean_object* v_w_143_; lean_object* v_n_144_; lean_object* v_expr_145_; lean_object* v___x_146_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_w_143_ = lean_ctor_get(v_expr_111_, 0);
lean_inc(v_w_143_);
v_n_144_ = lean_ctor_get(v_expr_111_, 2);
lean_inc(v_n_144_);
v_expr_145_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_expr_145_);
lean_dec_ref_known(v_expr_111_, 4);
v___x_146_ = lean_apply_5(v_h__6_117_, v_w_110_, v_w_143_, v_n_144_, v_expr_145_, lean_box(0));
return v___x_146_;
}
case 7:
{
lean_object* v_n_147_; lean_object* v_lhs_148_; lean_object* v_rhs_149_; lean_object* v___x_150_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__9_120_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_n_147_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_n_147_);
v_lhs_148_ = lean_ctor_get(v_expr_111_, 2);
lean_inc_ref(v_lhs_148_);
v_rhs_149_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_rhs_149_);
lean_dec_ref_known(v_expr_111_, 4);
v___x_150_ = lean_apply_4(v_h__8_119_, v_w_110_, v_n_147_, v_lhs_148_, v_rhs_149_);
return v___x_150_;
}
case 8:
{
lean_object* v_n_151_; lean_object* v_lhs_152_; lean_object* v_rhs_153_; lean_object* v___x_154_; 
lean_dec(v_h__10_121_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_n_151_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_n_151_);
v_lhs_152_ = lean_ctor_get(v_expr_111_, 2);
lean_inc_ref(v_lhs_152_);
v_rhs_153_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_rhs_153_);
lean_dec_ref_known(v_expr_111_, 4);
v___x_154_ = lean_apply_4(v_h__9_120_, v_w_110_, v_n_151_, v_lhs_152_, v_rhs_153_);
return v___x_154_;
}
default: 
{
lean_object* v_n_155_; lean_object* v_lhs_156_; lean_object* v_rhs_157_; lean_object* v___x_158_; 
lean_dec(v_h__9_120_);
lean_dec(v_h__8_119_);
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_n_155_ = lean_ctor_get(v_expr_111_, 1);
lean_inc(v_n_155_);
v_lhs_156_ = lean_ctor_get(v_expr_111_, 2);
lean_inc_ref(v_lhs_156_);
v_rhs_157_ = lean_ctor_get(v_expr_111_, 3);
lean_inc_ref(v_rhs_157_);
lean_dec_ref_known(v_expr_111_, 4);
v___x_158_ = lean_apply_4(v_h__10_121_, v_w_110_, v_n_155_, v_lhs_156_, v_rhs_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(lean_object* v_op_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_, lean_object* v_h__3_162_, lean_object* v_h__4_163_, lean_object* v_h__5_164_, lean_object* v_h__6_165_, lean_object* v_h__7_166_){
_start:
{
switch(lean_obj_tag(v_op_159_))
{
case 0:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__6_165_);
lean_dec(v_h__5_164_);
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_apply_1(v_h__1_160_, v___x_167_);
return v___x_168_;
}
case 1:
{
lean_object* v_n_169_; lean_object* v___x_170_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__6_165_);
lean_dec(v_h__5_164_);
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__1_160_);
v_n_169_ = lean_ctor_get(v_op_159_, 0);
lean_inc(v_n_169_);
lean_dec_ref_known(v_op_159_, 1);
v___x_170_ = lean_apply_1(v_h__2_161_, v_n_169_);
return v___x_170_;
}
case 2:
{
lean_object* v_n_171_; lean_object* v___x_172_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__6_165_);
lean_dec(v_h__5_164_);
lean_dec(v_h__4_163_);
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v_n_171_ = lean_ctor_get(v_op_159_, 0);
lean_inc(v_n_171_);
lean_dec_ref_known(v_op_159_, 1);
v___x_172_ = lean_apply_1(v_h__3_162_, v_n_171_);
return v___x_172_;
}
case 3:
{
lean_object* v_n_173_; lean_object* v___x_174_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__6_165_);
lean_dec(v_h__5_164_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v_n_173_ = lean_ctor_get(v_op_159_, 0);
lean_inc(v_n_173_);
lean_dec_ref_known(v_op_159_, 1);
v___x_174_ = lean_apply_1(v_h__4_163_, v_n_173_);
return v___x_174_;
}
case 4:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__6_165_);
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__5_164_, v___x_175_);
return v___x_176_;
}
case 5:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__7_166_);
lean_dec(v_h__5_164_);
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__6_165_, v___x_177_);
return v___x_178_;
}
default: 
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__6_165_);
lean_dec(v_h__5_164_);
lean_dec(v_h__4_163_);
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__7_166_, v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(lean_object* v_motive_181_, lean_object* v_op_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_, lean_object* v_h__3_185_, lean_object* v_h__4_186_, lean_object* v_h__5_187_, lean_object* v_h__6_188_, lean_object* v_h__7_189_){
_start:
{
switch(lean_obj_tag(v_op_182_))
{
case 0:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__6_188_);
lean_dec(v_h__5_187_);
lean_dec(v_h__4_186_);
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_1(v_h__1_183_, v___x_190_);
return v___x_191_;
}
case 1:
{
lean_object* v_n_192_; lean_object* v___x_193_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__6_188_);
lean_dec(v_h__5_187_);
lean_dec(v_h__4_186_);
lean_dec(v_h__3_185_);
lean_dec(v_h__1_183_);
v_n_192_ = lean_ctor_get(v_op_182_, 0);
lean_inc(v_n_192_);
lean_dec_ref_known(v_op_182_, 1);
v___x_193_ = lean_apply_1(v_h__2_184_, v_n_192_);
return v___x_193_;
}
case 2:
{
lean_object* v_n_194_; lean_object* v___x_195_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__6_188_);
lean_dec(v_h__5_187_);
lean_dec(v_h__4_186_);
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v_n_194_ = lean_ctor_get(v_op_182_, 0);
lean_inc(v_n_194_);
lean_dec_ref_known(v_op_182_, 1);
v___x_195_ = lean_apply_1(v_h__3_185_, v_n_194_);
return v___x_195_;
}
case 3:
{
lean_object* v_n_196_; lean_object* v___x_197_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__6_188_);
lean_dec(v_h__5_187_);
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v_n_196_ = lean_ctor_get(v_op_182_, 0);
lean_inc(v_n_196_);
lean_dec_ref_known(v_op_182_, 1);
v___x_197_ = lean_apply_1(v_h__4_186_, v_n_196_);
return v___x_197_;
}
case 4:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__6_188_);
lean_dec(v_h__4_186_);
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_1(v_h__5_187_, v___x_198_);
return v___x_199_;
}
case 5:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_h__7_189_);
lean_dec(v_h__5_187_);
lean_dec(v_h__4_186_);
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_1(v_h__6_188_, v___x_200_);
return v___x_201_;
}
default: 
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_h__6_188_);
lean_dec(v_h__5_187_);
lean_dec(v_h__4_186_);
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_1(v_h__7_189_, v___x_202_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(uint8_t v_op_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_, lean_object* v_h__3_207_, lean_object* v_h__4_208_, lean_object* v_h__5_209_, lean_object* v_h__6_210_, lean_object* v_h__7_211_){
_start:
{
switch(v_op_204_)
{
case 0:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__6_210_);
lean_dec(v_h__5_209_);
lean_dec(v_h__4_208_);
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_1(v_h__1_205_, v___x_212_);
return v___x_213_;
}
case 1:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__6_210_);
lean_dec(v_h__5_209_);
lean_dec(v_h__4_208_);
lean_dec(v_h__3_207_);
lean_dec(v_h__1_205_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__2_206_, v___x_214_);
return v___x_215_;
}
case 2:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__6_210_);
lean_dec(v_h__5_209_);
lean_dec(v_h__4_208_);
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v_h__3_207_, v___x_216_);
return v___x_217_;
}
case 3:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__6_210_);
lean_dec(v_h__5_209_);
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_apply_1(v_h__4_208_, v___x_218_);
return v___x_219_;
}
case 4:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__6_210_);
lean_dec(v_h__4_208_);
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_apply_1(v_h__5_209_, v___x_220_);
return v___x_221_;
}
case 5:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v_h__7_211_);
lean_dec(v_h__5_209_);
lean_dec(v_h__4_208_);
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_apply_1(v_h__6_210_, v___x_222_);
return v___x_223_;
}
default: 
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_h__6_210_);
lean_dec(v_h__5_209_);
lean_dec(v_h__4_208_);
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_apply_1(v_h__7_211_, v___x_224_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(lean_object* v_op_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_, lean_object* v_h__3_229_, lean_object* v_h__4_230_, lean_object* v_h__5_231_, lean_object* v_h__6_232_, lean_object* v_h__7_233_){
_start:
{
uint8_t v_op_69__boxed_234_; lean_object* v_res_235_; 
v_op_69__boxed_234_ = lean_unbox(v_op_226_);
v_res_235_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_69__boxed_234_, v_h__1_227_, v_h__2_228_, v_h__3_229_, v_h__4_230_, v_h__5_231_, v_h__6_232_, v_h__7_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(lean_object* v_motive_236_, uint8_t v_op_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_, lean_object* v_h__3_240_, lean_object* v_h__4_241_, lean_object* v_h__5_242_, lean_object* v_h__6_243_, lean_object* v_h__7_244_){
_start:
{
switch(v_op_237_)
{
case 0:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__6_243_);
lean_dec(v_h__5_242_);
lean_dec(v_h__4_241_);
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_apply_1(v_h__1_238_, v___x_245_);
return v___x_246_;
}
case 1:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__6_243_);
lean_dec(v_h__5_242_);
lean_dec(v_h__4_241_);
lean_dec(v_h__3_240_);
lean_dec(v_h__1_238_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_h__2_239_, v___x_247_);
return v___x_248_;
}
case 2:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__6_243_);
lean_dec(v_h__5_242_);
lean_dec(v_h__4_241_);
lean_dec(v_h__2_239_);
lean_dec(v_h__1_238_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_apply_1(v_h__3_240_, v___x_249_);
return v___x_250_;
}
case 3:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__6_243_);
lean_dec(v_h__5_242_);
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
lean_dec(v_h__1_238_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_apply_1(v_h__4_241_, v___x_251_);
return v___x_252_;
}
case 4:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__6_243_);
lean_dec(v_h__4_241_);
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
lean_dec(v_h__1_238_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_apply_1(v_h__5_242_, v___x_253_);
return v___x_254_;
}
case 5:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_h__7_244_);
lean_dec(v_h__5_242_);
lean_dec(v_h__4_241_);
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
lean_dec(v_h__1_238_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_h__6_243_, v___x_255_);
return v___x_256_;
}
default: 
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_h__6_243_);
lean_dec(v_h__5_242_);
lean_dec(v_h__4_241_);
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
lean_dec(v_h__1_238_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_1(v_h__7_244_, v___x_257_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(lean_object* v_motive_259_, lean_object* v_op_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_, lean_object* v_h__3_263_, lean_object* v_h__4_264_, lean_object* v_h__5_265_, lean_object* v_h__6_266_, lean_object* v_h__7_267_){
_start:
{
uint8_t v_op_100__boxed_268_; lean_object* v_res_269_; 
v_op_100__boxed_268_ = lean_unbox(v_op_260_);
v_res_269_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_259_, v_op_100__boxed_268_, v_h__1_261_, v_h__2_262_, v_h__3_263_, v_h__4_264_, v_h__5_265_, v_h__6_266_, v_h__7_267_);
return v_res_269_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ShiftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Replicate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_RotateRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Reverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Cpop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
}
#ifdef __cplusplus
}
#endif
