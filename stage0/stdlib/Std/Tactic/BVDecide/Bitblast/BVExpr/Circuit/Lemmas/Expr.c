// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr import Init.ByCases import Init.Data.Nat.Linear import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
lean_dec_ref(v_x_1_);
v___x_6_ = lean_apply_2(v_h__1_2_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(lean_object* v_w_7_, lean_object* v_expr_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_apply_1(v_h__2_12_, lean_box(0));
return v___x_13_;
}
else
{
lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_12_);
v_val_14_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_14_);
lean_dec_ref(v_x_10_);
v___x_15_ = lean_apply_2(v_h__1_11_, v_val_14_, lean_box(0));
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(lean_object* v_w_16_, lean_object* v_expr_17_, lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_16_, v_expr_17_, v_motive_18_, v_x_19_, v_h__1_20_, v_h__2_21_);
lean_dec_ref(v_expr_17_);
lean_dec(v_w_16_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
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
lean_dec_ref(v_x_23_);
v___x_29_ = lean_apply_1(v_h__1_24_, v_val_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(lean_object* v_w_30_, lean_object* v_aig_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_34_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__2_35_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_val_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v_val_38_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_val_38_);
lean_dec_ref(v_x_33_);
v___x_39_ = lean_apply_1(v_h__1_34_, v_val_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(lean_object* v_w_40_, lean_object* v_aig_41_, lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_40_, v_aig_41_, v_motive_42_, v_x_43_, v_h__1_44_, v_h__2_45_);
lean_dec_ref(v_aig_41_);
lean_dec(v_w_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(lean_object* v_w_47_, lean_object* v_expr_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_, lean_object* v_h__4_52_, lean_object* v_h__5_53_, lean_object* v_h__6_54_, lean_object* v_h__7_55_, lean_object* v_h__8_56_, lean_object* v_h__9_57_, lean_object* v_h__10_58_){
_start:
{
switch(lean_obj_tag(v_expr_48_))
{
case 0:
{
lean_object* v_idx_59_; lean_object* v___x_60_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
v_idx_59_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_idx_59_);
lean_dec_ref(v_expr_48_);
v___x_60_ = lean_apply_2(v_h__1_49_, v_w_47_, v_idx_59_);
return v___x_60_;
}
case 1:
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__1_49_);
v_val_61_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_val_61_);
lean_dec_ref(v_expr_48_);
v___x_62_ = lean_apply_2(v_h__2_50_, v_w_47_, v_val_61_);
return v___x_62_;
}
case 2:
{
lean_object* v_w_63_; lean_object* v_start_64_; lean_object* v_expr_65_; lean_object* v___x_66_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_w_63_ = lean_ctor_get(v_expr_48_, 0);
lean_inc(v_w_63_);
v_start_64_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_start_64_);
v_expr_65_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_expr_65_);
lean_dec_ref(v_expr_48_);
v___x_66_ = lean_apply_4(v_h__7_55_, v_w_47_, v_w_63_, v_start_64_, v_expr_65_);
return v___x_66_;
}
case 3:
{
lean_object* v_lhs_67_; uint8_t v_op_68_; lean_object* v_rhs_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_lhs_67_ = lean_ctor_get(v_expr_48_, 1);
lean_inc_ref(v_lhs_67_);
v_op_68_ = lean_ctor_get_uint8(v_expr_48_, sizeof(void*)*3 + 8);
v_rhs_69_ = lean_ctor_get(v_expr_48_, 2);
lean_inc_ref(v_rhs_69_);
lean_dec_ref(v_expr_48_);
v___x_70_ = lean_box(v_op_68_);
v___x_71_ = lean_apply_4(v_h__3_51_, v_w_47_, v_lhs_67_, v___x_70_, v_rhs_69_);
return v___x_71_;
}
case 4:
{
lean_object* v_op_72_; lean_object* v_operand_73_; lean_object* v___x_74_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_op_72_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_op_72_);
v_operand_73_ = lean_ctor_get(v_expr_48_, 2);
lean_inc_ref(v_operand_73_);
lean_dec_ref(v_expr_48_);
v___x_74_ = lean_apply_3(v_h__4_52_, v_w_47_, v_op_72_, v_operand_73_);
return v___x_74_;
}
case 5:
{
lean_object* v_l_75_; lean_object* v_r_76_; lean_object* v_lhs_77_; lean_object* v_rhs_78_; lean_object* v___x_79_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_l_75_ = lean_ctor_get(v_expr_48_, 0);
lean_inc(v_l_75_);
v_r_76_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_r_76_);
v_lhs_77_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_lhs_77_);
v_rhs_78_ = lean_ctor_get(v_expr_48_, 4);
lean_inc_ref(v_rhs_78_);
lean_dec_ref(v_expr_48_);
v___x_79_ = lean_apply_6(v_h__5_53_, v_w_47_, v_l_75_, v_r_76_, v_lhs_77_, v_rhs_78_, lean_box(0));
return v___x_79_;
}
case 6:
{
lean_object* v_w_80_; lean_object* v_n_81_; lean_object* v_expr_82_; lean_object* v___x_83_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_w_80_ = lean_ctor_get(v_expr_48_, 0);
lean_inc(v_w_80_);
v_n_81_ = lean_ctor_get(v_expr_48_, 2);
lean_inc(v_n_81_);
v_expr_82_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_expr_82_);
lean_dec_ref(v_expr_48_);
v___x_83_ = lean_apply_5(v_h__6_54_, v_w_47_, v_w_80_, v_n_81_, v_expr_82_, lean_box(0));
return v___x_83_;
}
case 7:
{
lean_object* v_n_84_; lean_object* v_lhs_85_; lean_object* v_rhs_86_; lean_object* v___x_87_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__9_57_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_n_84_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_n_84_);
v_lhs_85_ = lean_ctor_get(v_expr_48_, 2);
lean_inc_ref(v_lhs_85_);
v_rhs_86_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_rhs_86_);
lean_dec_ref(v_expr_48_);
v___x_87_ = lean_apply_4(v_h__8_56_, v_w_47_, v_n_84_, v_lhs_85_, v_rhs_86_);
return v___x_87_;
}
case 8:
{
lean_object* v_n_88_; lean_object* v_lhs_89_; lean_object* v_rhs_90_; lean_object* v___x_91_; 
lean_dec(v_h__10_58_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_n_88_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_n_88_);
v_lhs_89_ = lean_ctor_get(v_expr_48_, 2);
lean_inc_ref(v_lhs_89_);
v_rhs_90_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_rhs_90_);
lean_dec_ref(v_expr_48_);
v___x_91_ = lean_apply_4(v_h__9_57_, v_w_47_, v_n_88_, v_lhs_89_, v_rhs_90_);
return v___x_91_;
}
default: 
{
lean_object* v_n_92_; lean_object* v_lhs_93_; lean_object* v_rhs_94_; lean_object* v___x_95_; 
lean_dec(v_h__9_57_);
lean_dec(v_h__8_56_);
lean_dec(v_h__7_55_);
lean_dec(v_h__6_54_);
lean_dec(v_h__5_53_);
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_n_92_ = lean_ctor_get(v_expr_48_, 1);
lean_inc(v_n_92_);
v_lhs_93_ = lean_ctor_get(v_expr_48_, 2);
lean_inc_ref(v_lhs_93_);
v_rhs_94_ = lean_ctor_get(v_expr_48_, 3);
lean_inc_ref(v_rhs_94_);
lean_dec_ref(v_expr_48_);
v___x_95_ = lean_apply_4(v_h__10_58_, v_w_47_, v_n_92_, v_lhs_93_, v_rhs_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(lean_object* v_motive_96_, lean_object* v_w_97_, lean_object* v_expr_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_, lean_object* v_h__3_101_, lean_object* v_h__4_102_, lean_object* v_h__5_103_, lean_object* v_h__6_104_, lean_object* v_h__7_105_, lean_object* v_h__8_106_, lean_object* v_h__9_107_, lean_object* v_h__10_108_){
_start:
{
switch(lean_obj_tag(v_expr_98_))
{
case 0:
{
lean_object* v_idx_109_; lean_object* v___x_110_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
v_idx_109_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_idx_109_);
lean_dec_ref(v_expr_98_);
v___x_110_ = lean_apply_2(v_h__1_99_, v_w_97_, v_idx_109_);
return v___x_110_;
}
case 1:
{
lean_object* v_val_111_; lean_object* v___x_112_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__1_99_);
v_val_111_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_val_111_);
lean_dec_ref(v_expr_98_);
v___x_112_ = lean_apply_2(v_h__2_100_, v_w_97_, v_val_111_);
return v___x_112_;
}
case 2:
{
lean_object* v_w_113_; lean_object* v_start_114_; lean_object* v_expr_115_; lean_object* v___x_116_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_w_113_ = lean_ctor_get(v_expr_98_, 0);
lean_inc(v_w_113_);
v_start_114_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_start_114_);
v_expr_115_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_expr_115_);
lean_dec_ref(v_expr_98_);
v___x_116_ = lean_apply_4(v_h__7_105_, v_w_97_, v_w_113_, v_start_114_, v_expr_115_);
return v___x_116_;
}
case 3:
{
lean_object* v_lhs_117_; uint8_t v_op_118_; lean_object* v_rhs_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_lhs_117_ = lean_ctor_get(v_expr_98_, 1);
lean_inc_ref(v_lhs_117_);
v_op_118_ = lean_ctor_get_uint8(v_expr_98_, sizeof(void*)*3 + 8);
v_rhs_119_ = lean_ctor_get(v_expr_98_, 2);
lean_inc_ref(v_rhs_119_);
lean_dec_ref(v_expr_98_);
v___x_120_ = lean_box(v_op_118_);
v___x_121_ = lean_apply_4(v_h__3_101_, v_w_97_, v_lhs_117_, v___x_120_, v_rhs_119_);
return v___x_121_;
}
case 4:
{
lean_object* v_op_122_; lean_object* v_operand_123_; lean_object* v___x_124_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_op_122_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_op_122_);
v_operand_123_ = lean_ctor_get(v_expr_98_, 2);
lean_inc_ref(v_operand_123_);
lean_dec_ref(v_expr_98_);
v___x_124_ = lean_apply_3(v_h__4_102_, v_w_97_, v_op_122_, v_operand_123_);
return v___x_124_;
}
case 5:
{
lean_object* v_l_125_; lean_object* v_r_126_; lean_object* v_lhs_127_; lean_object* v_rhs_128_; lean_object* v___x_129_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_l_125_ = lean_ctor_get(v_expr_98_, 0);
lean_inc(v_l_125_);
v_r_126_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_r_126_);
v_lhs_127_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_lhs_127_);
v_rhs_128_ = lean_ctor_get(v_expr_98_, 4);
lean_inc_ref(v_rhs_128_);
lean_dec_ref(v_expr_98_);
v___x_129_ = lean_apply_6(v_h__5_103_, v_w_97_, v_l_125_, v_r_126_, v_lhs_127_, v_rhs_128_, lean_box(0));
return v___x_129_;
}
case 6:
{
lean_object* v_w_130_; lean_object* v_n_131_; lean_object* v_expr_132_; lean_object* v___x_133_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_w_130_ = lean_ctor_get(v_expr_98_, 0);
lean_inc(v_w_130_);
v_n_131_ = lean_ctor_get(v_expr_98_, 2);
lean_inc(v_n_131_);
v_expr_132_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_expr_132_);
lean_dec_ref(v_expr_98_);
v___x_133_ = lean_apply_5(v_h__6_104_, v_w_97_, v_w_130_, v_n_131_, v_expr_132_, lean_box(0));
return v___x_133_;
}
case 7:
{
lean_object* v_n_134_; lean_object* v_lhs_135_; lean_object* v_rhs_136_; lean_object* v___x_137_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__9_107_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_n_134_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_n_134_);
v_lhs_135_ = lean_ctor_get(v_expr_98_, 2);
lean_inc_ref(v_lhs_135_);
v_rhs_136_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_rhs_136_);
lean_dec_ref(v_expr_98_);
v___x_137_ = lean_apply_4(v_h__8_106_, v_w_97_, v_n_134_, v_lhs_135_, v_rhs_136_);
return v___x_137_;
}
case 8:
{
lean_object* v_n_138_; lean_object* v_lhs_139_; lean_object* v_rhs_140_; lean_object* v___x_141_; 
lean_dec(v_h__10_108_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_n_138_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_n_138_);
v_lhs_139_ = lean_ctor_get(v_expr_98_, 2);
lean_inc_ref(v_lhs_139_);
v_rhs_140_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_rhs_140_);
lean_dec_ref(v_expr_98_);
v___x_141_ = lean_apply_4(v_h__9_107_, v_w_97_, v_n_138_, v_lhs_139_, v_rhs_140_);
return v___x_141_;
}
default: 
{
lean_object* v_n_142_; lean_object* v_lhs_143_; lean_object* v_rhs_144_; lean_object* v___x_145_; 
lean_dec(v_h__9_107_);
lean_dec(v_h__8_106_);
lean_dec(v_h__7_105_);
lean_dec(v_h__6_104_);
lean_dec(v_h__5_103_);
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_n_142_ = lean_ctor_get(v_expr_98_, 1);
lean_inc(v_n_142_);
v_lhs_143_ = lean_ctor_get(v_expr_98_, 2);
lean_inc_ref(v_lhs_143_);
v_rhs_144_ = lean_ctor_get(v_expr_98_, 3);
lean_inc_ref(v_rhs_144_);
lean_dec_ref(v_expr_98_);
v___x_145_ = lean_apply_4(v_h__10_108_, v_w_97_, v_n_142_, v_lhs_143_, v_rhs_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(lean_object* v_op_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_, lean_object* v_h__3_149_, lean_object* v_h__4_150_, lean_object* v_h__5_151_, lean_object* v_h__6_152_, lean_object* v_h__7_153_){
_start:
{
switch(lean_obj_tag(v_op_146_))
{
case 0:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_apply_1(v_h__1_147_, v___x_154_);
return v___x_155_;
}
case 1:
{
lean_object* v_n_156_; lean_object* v___x_157_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
lean_dec(v_h__1_147_);
v_n_156_ = lean_ctor_get(v_op_146_, 0);
lean_inc(v_n_156_);
lean_dec_ref(v_op_146_);
v___x_157_ = lean_apply_1(v_h__2_148_, v_n_156_);
return v___x_157_;
}
case 2:
{
lean_object* v_n_158_; lean_object* v___x_159_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
v_n_158_ = lean_ctor_get(v_op_146_, 0);
lean_inc(v_n_158_);
lean_dec_ref(v_op_146_);
v___x_159_ = lean_apply_1(v_h__3_149_, v_n_158_);
return v___x_159_;
}
case 3:
{
lean_object* v_n_160_; lean_object* v___x_161_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
v_n_160_ = lean_ctor_get(v_op_146_, 0);
lean_inc(v_n_160_);
lean_dec_ref(v_op_146_);
v___x_161_ = lean_apply_1(v_h__4_150_, v_n_160_);
return v___x_161_;
}
case 4:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_apply_1(v_h__5_151_, v___x_162_);
return v___x_163_;
}
case 5:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__6_152_, v___x_164_);
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__7_153_, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(lean_object* v_motive_168_, lean_object* v_op_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_, lean_object* v_h__3_172_, lean_object* v_h__4_173_, lean_object* v_h__5_174_, lean_object* v_h__6_175_, lean_object* v_h__7_176_){
_start:
{
switch(lean_obj_tag(v_op_169_))
{
case 0:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__6_175_);
lean_dec(v_h__5_174_);
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__1_170_, v___x_177_);
return v___x_178_;
}
case 1:
{
lean_object* v_n_179_; lean_object* v___x_180_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__6_175_);
lean_dec(v_h__5_174_);
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__1_170_);
v_n_179_ = lean_ctor_get(v_op_169_, 0);
lean_inc(v_n_179_);
lean_dec_ref(v_op_169_);
v___x_180_ = lean_apply_1(v_h__2_171_, v_n_179_);
return v___x_180_;
}
case 2:
{
lean_object* v_n_181_; lean_object* v___x_182_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__6_175_);
lean_dec(v_h__5_174_);
lean_dec(v_h__4_173_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v_n_181_ = lean_ctor_get(v_op_169_, 0);
lean_inc(v_n_181_);
lean_dec_ref(v_op_169_);
v___x_182_ = lean_apply_1(v_h__3_172_, v_n_181_);
return v___x_182_;
}
case 3:
{
lean_object* v_n_183_; lean_object* v___x_184_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__6_175_);
lean_dec(v_h__5_174_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v_n_183_ = lean_ctor_get(v_op_169_, 0);
lean_inc(v_n_183_);
lean_dec_ref(v_op_169_);
v___x_184_ = lean_apply_1(v_h__4_173_, v_n_183_);
return v___x_184_;
}
case 4:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__6_175_);
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_1(v_h__5_174_, v___x_185_);
return v___x_186_;
}
case 5:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_h__7_176_);
lean_dec(v_h__5_174_);
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_h__6_175_, v___x_187_);
return v___x_188_;
}
default: 
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_h__6_175_);
lean_dec(v_h__5_174_);
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_apply_1(v_h__7_176_, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(uint8_t v_op_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_, lean_object* v_h__3_194_, lean_object* v_h__4_195_, lean_object* v_h__5_196_, lean_object* v_h__6_197_, lean_object* v_h__7_198_){
_start:
{
switch(v_op_191_)
{
case 0:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__6_197_);
lean_dec(v_h__5_196_);
lean_dec(v_h__4_195_);
lean_dec(v_h__3_194_);
lean_dec(v_h__2_193_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__1_192_, v___x_199_);
return v___x_200_;
}
case 1:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__6_197_);
lean_dec(v_h__5_196_);
lean_dec(v_h__4_195_);
lean_dec(v_h__3_194_);
lean_dec(v_h__1_192_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_1(v_h__2_193_, v___x_201_);
return v___x_202_;
}
case 2:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__6_197_);
lean_dec(v_h__5_196_);
lean_dec(v_h__4_195_);
lean_dec(v_h__2_193_);
lean_dec(v_h__1_192_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__3_194_, v___x_203_);
return v___x_204_;
}
case 3:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__6_197_);
lean_dec(v_h__5_196_);
lean_dec(v_h__3_194_);
lean_dec(v_h__2_193_);
lean_dec(v_h__1_192_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__4_195_, v___x_205_);
return v___x_206_;
}
case 4:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__6_197_);
lean_dec(v_h__4_195_);
lean_dec(v_h__3_194_);
lean_dec(v_h__2_193_);
lean_dec(v_h__1_192_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_h__5_196_, v___x_207_);
return v___x_208_;
}
case 5:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_h__7_198_);
lean_dec(v_h__5_196_);
lean_dec(v_h__4_195_);
lean_dec(v_h__3_194_);
lean_dec(v_h__2_193_);
lean_dec(v_h__1_192_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_apply_1(v_h__6_197_, v___x_209_);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__6_197_);
lean_dec(v_h__5_196_);
lean_dec(v_h__4_195_);
lean_dec(v_h__3_194_);
lean_dec(v_h__2_193_);
lean_dec(v_h__1_192_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__7_198_, v___x_211_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(lean_object* v_op_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_, lean_object* v_h__3_216_, lean_object* v_h__4_217_, lean_object* v_h__5_218_, lean_object* v_h__6_219_, lean_object* v_h__7_220_){
_start:
{
uint8_t v_op_76__boxed_221_; lean_object* v_res_222_; 
v_op_76__boxed_221_ = lean_unbox(v_op_213_);
v_res_222_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_76__boxed_221_, v_h__1_214_, v_h__2_215_, v_h__3_216_, v_h__4_217_, v_h__5_218_, v_h__6_219_, v_h__7_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(lean_object* v_motive_223_, uint8_t v_op_224_, lean_object* v_h__1_225_, lean_object* v_h__2_226_, lean_object* v_h__3_227_, lean_object* v_h__4_228_, lean_object* v_h__5_229_, lean_object* v_h__6_230_, lean_object* v_h__7_231_){
_start:
{
switch(v_op_224_)
{
case 0:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__6_230_);
lean_dec(v_h__5_229_);
lean_dec(v_h__4_228_);
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_h__1_225_, v___x_232_);
return v___x_233_;
}
case 1:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__6_230_);
lean_dec(v_h__5_229_);
lean_dec(v_h__4_228_);
lean_dec(v_h__3_227_);
lean_dec(v_h__1_225_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_h__2_226_, v___x_234_);
return v___x_235_;
}
case 2:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__6_230_);
lean_dec(v_h__5_229_);
lean_dec(v_h__4_228_);
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__3_227_, v___x_236_);
return v___x_237_;
}
case 3:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__6_230_);
lean_dec(v_h__5_229_);
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_1(v_h__4_228_, v___x_238_);
return v___x_239_;
}
case 4:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__6_230_);
lean_dec(v_h__4_228_);
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_1(v_h__5_229_, v___x_240_);
return v___x_241_;
}
case 5:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__7_231_);
lean_dec(v_h__5_229_);
lean_dec(v_h__4_228_);
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__6_230_, v___x_242_);
return v___x_243_;
}
default: 
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__6_230_);
lean_dec(v_h__5_229_);
lean_dec(v_h__4_228_);
lean_dec(v_h__3_227_);
lean_dec(v_h__2_226_);
lean_dec(v_h__1_225_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__7_231_, v___x_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(lean_object* v_motive_246_, lean_object* v_op_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_, lean_object* v_h__3_250_, lean_object* v_h__4_251_, lean_object* v_h__5_252_, lean_object* v_h__6_253_, lean_object* v_h__7_254_){
_start:
{
uint8_t v_op_107__boxed_255_; lean_object* v_res_256_; 
v_op_107__boxed_255_ = lean_unbox(v_op_247_);
v_res_256_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_246_, v_op_107__boxed_255_, v_h__1_248_, v_h__2_249_, v_h__3_250_, v_h__4_251_, v_h__5_252_, v_h__6_253_, v_h__7_254_);
return v_res_256_;
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
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
