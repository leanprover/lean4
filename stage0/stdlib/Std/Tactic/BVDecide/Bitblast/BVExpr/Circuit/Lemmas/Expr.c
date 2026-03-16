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
lean_object* v___x_13_; 
v___x_13_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter___boxed(lean_object* v_w_14_, lean_object* v_expr_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_Cache_get_x3f_match__1_splitter(v_w_14_, v_expr_15_, v_motive_16_, v_x_17_, v_h__1_18_, v_h__2_19_);
lean_dec_ref(v_expr_15_);
lean_dec(v_w_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__2_23_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_23_);
v_val_26_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref(v_x_21_);
v___x_27_ = lean_apply_1(v_h__1_22_, v_val_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(lean_object* v_w_28_, lean_object* v_aig_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___redArg(v_x_31_, v_h__1_32_, v_h__2_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter___boxed(lean_object* v_w_35_, lean_object* v_aig_36_, lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_goCache_match__3_splitter(v_w_35_, v_aig_36_, v_motive_37_, v_x_38_, v_h__1_39_, v_h__2_40_);
lean_dec_ref(v_aig_36_);
lean_dec(v_w_35_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(lean_object* v_w_42_, lean_object* v_expr_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_, lean_object* v_h__4_47_, lean_object* v_h__5_48_, lean_object* v_h__6_49_, lean_object* v_h__7_50_, lean_object* v_h__8_51_, lean_object* v_h__9_52_, lean_object* v_h__10_53_){
_start:
{
switch(lean_obj_tag(v_expr_43_))
{
case 0:
{
lean_object* v_idx_54_; lean_object* v___x_55_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v_idx_54_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_idx_54_);
lean_dec_ref(v_expr_43_);
v___x_55_ = lean_apply_2(v_h__1_44_, v_w_42_, v_idx_54_);
return v___x_55_;
}
case 1:
{
lean_object* v_val_56_; lean_object* v___x_57_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v_val_56_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_val_56_);
lean_dec_ref(v_expr_43_);
v___x_57_ = lean_apply_2(v_h__2_45_, v_w_42_, v_val_56_);
return v___x_57_;
}
case 2:
{
lean_object* v_w_58_; lean_object* v_start_59_; lean_object* v_expr_60_; lean_object* v___x_61_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_w_58_ = lean_ctor_get(v_expr_43_, 0);
lean_inc(v_w_58_);
v_start_59_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_start_59_);
v_expr_60_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_expr_60_);
lean_dec_ref(v_expr_43_);
v___x_61_ = lean_apply_4(v_h__7_50_, v_w_42_, v_w_58_, v_start_59_, v_expr_60_);
return v___x_61_;
}
case 3:
{
lean_object* v_lhs_62_; uint8_t v_op_63_; lean_object* v_rhs_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_lhs_62_ = lean_ctor_get(v_expr_43_, 1);
lean_inc_ref(v_lhs_62_);
v_op_63_ = lean_ctor_get_uint8(v_expr_43_, sizeof(void*)*3 + 8);
v_rhs_64_ = lean_ctor_get(v_expr_43_, 2);
lean_inc_ref(v_rhs_64_);
lean_dec_ref(v_expr_43_);
v___x_65_ = lean_box(v_op_63_);
v___x_66_ = lean_apply_4(v_h__3_46_, v_w_42_, v_lhs_62_, v___x_65_, v_rhs_64_);
return v___x_66_;
}
case 4:
{
lean_object* v_op_67_; lean_object* v_operand_68_; lean_object* v___x_69_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_op_67_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_op_67_);
v_operand_68_ = lean_ctor_get(v_expr_43_, 2);
lean_inc_ref(v_operand_68_);
lean_dec_ref(v_expr_43_);
v___x_69_ = lean_apply_3(v_h__4_47_, v_w_42_, v_op_67_, v_operand_68_);
return v___x_69_;
}
case 5:
{
lean_object* v_l_70_; lean_object* v_r_71_; lean_object* v_lhs_72_; lean_object* v_rhs_73_; lean_object* v___x_74_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_l_70_ = lean_ctor_get(v_expr_43_, 0);
lean_inc(v_l_70_);
v_r_71_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_r_71_);
v_lhs_72_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_lhs_72_);
v_rhs_73_ = lean_ctor_get(v_expr_43_, 4);
lean_inc_ref(v_rhs_73_);
lean_dec_ref(v_expr_43_);
v___x_74_ = lean_apply_6(v_h__5_48_, v_w_42_, v_l_70_, v_r_71_, v_lhs_72_, v_rhs_73_, lean_box(0));
return v___x_74_;
}
case 6:
{
lean_object* v_w_75_; lean_object* v_n_76_; lean_object* v_expr_77_; lean_object* v___x_78_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_w_75_ = lean_ctor_get(v_expr_43_, 0);
lean_inc(v_w_75_);
v_n_76_ = lean_ctor_get(v_expr_43_, 2);
lean_inc(v_n_76_);
v_expr_77_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_expr_77_);
lean_dec_ref(v_expr_43_);
v___x_78_ = lean_apply_5(v_h__6_49_, v_w_42_, v_w_75_, v_n_76_, v_expr_77_, lean_box(0));
return v___x_78_;
}
case 7:
{
lean_object* v_n_79_; lean_object* v_lhs_80_; lean_object* v_rhs_81_; lean_object* v___x_82_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__9_52_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_n_79_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_n_79_);
v_lhs_80_ = lean_ctor_get(v_expr_43_, 2);
lean_inc_ref(v_lhs_80_);
v_rhs_81_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_rhs_81_);
lean_dec_ref(v_expr_43_);
v___x_82_ = lean_apply_4(v_h__8_51_, v_w_42_, v_n_79_, v_lhs_80_, v_rhs_81_);
return v___x_82_;
}
case 8:
{
lean_object* v_n_83_; lean_object* v_lhs_84_; lean_object* v_rhs_85_; lean_object* v___x_86_; 
lean_dec(v_h__10_53_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_n_83_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_n_83_);
v_lhs_84_ = lean_ctor_get(v_expr_43_, 2);
lean_inc_ref(v_lhs_84_);
v_rhs_85_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_rhs_85_);
lean_dec_ref(v_expr_43_);
v___x_86_ = lean_apply_4(v_h__9_52_, v_w_42_, v_n_83_, v_lhs_84_, v_rhs_85_);
return v___x_86_;
}
default: 
{
lean_object* v_n_87_; lean_object* v_lhs_88_; lean_object* v_rhs_89_; lean_object* v___x_90_; 
lean_dec(v_h__9_52_);
lean_dec(v_h__8_51_);
lean_dec(v_h__7_50_);
lean_dec(v_h__6_49_);
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_n_87_ = lean_ctor_get(v_expr_43_, 1);
lean_inc(v_n_87_);
v_lhs_88_ = lean_ctor_get(v_expr_43_, 2);
lean_inc_ref(v_lhs_88_);
v_rhs_89_ = lean_ctor_get(v_expr_43_, 3);
lean_inc_ref(v_rhs_89_);
lean_dec_ref(v_expr_43_);
v___x_90_ = lean_apply_4(v_h__10_53_, v_w_42_, v_n_87_, v_lhs_88_, v_rhs_89_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter(lean_object* v_motive_91_, lean_object* v_w_92_, lean_object* v_expr_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_, lean_object* v_h__4_97_, lean_object* v_h__5_98_, lean_object* v_h__6_99_, lean_object* v_h__7_100_, lean_object* v_h__8_101_, lean_object* v_h__9_102_, lean_object* v_h__10_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__17_splitter___redArg(v_w_92_, v_expr_93_, v_h__1_94_, v_h__2_95_, v_h__3_96_, v_h__4_97_, v_h__5_98_, v_h__6_99_, v_h__7_100_, v_h__8_101_, v_h__9_102_, v_h__10_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(lean_object* v_op_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_, lean_object* v_h__4_109_, lean_object* v_h__5_110_, lean_object* v_h__6_111_, lean_object* v_h__7_112_){
_start:
{
switch(lean_obj_tag(v_op_105_))
{
case 0:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__6_111_);
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__1_106_, v___x_113_);
return v___x_114_;
}
case 1:
{
lean_object* v_n_115_; lean_object* v___x_116_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__6_111_);
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
lean_dec(v_h__3_108_);
lean_dec(v_h__1_106_);
v_n_115_ = lean_ctor_get(v_op_105_, 0);
lean_inc(v_n_115_);
lean_dec_ref(v_op_105_);
v___x_116_ = lean_apply_1(v_h__2_107_, v_n_115_);
return v___x_116_;
}
case 2:
{
lean_object* v_n_117_; lean_object* v___x_118_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__6_111_);
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v_n_117_ = lean_ctor_get(v_op_105_, 0);
lean_inc(v_n_117_);
lean_dec_ref(v_op_105_);
v___x_118_ = lean_apply_1(v_h__3_108_, v_n_117_);
return v___x_118_;
}
case 3:
{
lean_object* v_n_119_; lean_object* v___x_120_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__6_111_);
lean_dec(v_h__5_110_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v_n_119_ = lean_ctor_get(v_op_105_, 0);
lean_inc(v_n_119_);
lean_dec_ref(v_op_105_);
v___x_120_ = lean_apply_1(v_h__4_109_, v_n_119_);
return v___x_120_;
}
case 4:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__6_111_);
lean_dec(v_h__4_109_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__5_110_, v___x_121_);
return v___x_122_;
}
case 5:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_h__7_112_);
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v_h__6_111_, v___x_123_);
return v___x_124_;
}
default: 
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_h__6_111_);
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_1(v_h__7_112_, v___x_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter(lean_object* v_motive_127_, lean_object* v_op_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_, lean_object* v_h__3_131_, lean_object* v_h__4_132_, lean_object* v_h__5_133_, lean_object* v_h__6_134_, lean_object* v_h__7_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__15_splitter___redArg(v_op_128_, v_h__1_129_, v_h__2_130_, v_h__3_131_, v_h__4_132_, v_h__5_133_, v_h__6_134_, v_h__7_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(uint8_t v_op_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_, lean_object* v_h__3_140_, lean_object* v_h__4_141_, lean_object* v_h__5_142_, lean_object* v_h__6_143_, lean_object* v_h__7_144_){
_start:
{
switch(v_op_137_)
{
case 0:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__1_138_, v___x_145_);
return v___x_146_;
}
case 1:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__1_138_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__2_139_, v___x_147_);
return v___x_148_;
}
case 2:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__3_140_, v___x_149_);
return v___x_150_;
}
case 3:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v_h__4_141_, v___x_151_);
return v___x_152_;
}
case 4:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_1(v_h__5_142_, v___x_153_);
return v___x_154_;
}
case 5:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__6_143_, v___x_155_);
return v___x_156_;
}
default: 
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__7_144_, v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg___boxed(lean_object* v_op_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_, lean_object* v_h__3_162_, lean_object* v_h__4_163_, lean_object* v_h__5_164_, lean_object* v_h__6_165_, lean_object* v_h__7_166_){
_start:
{
uint8_t v_op_62__boxed_167_; lean_object* v_res_168_; 
v_op_62__boxed_167_ = lean_unbox(v_op_159_);
v_res_168_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_62__boxed_167_, v_h__1_160_, v_h__2_161_, v_h__3_162_, v_h__4_163_, v_h__5_164_, v_h__6_165_, v_h__7_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(lean_object* v_motive_169_, uint8_t v_op_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_, lean_object* v_h__3_173_, lean_object* v_h__4_174_, lean_object* v_h__5_175_, lean_object* v_h__6_176_, lean_object* v_h__7_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___redArg(v_op_170_, v_h__1_171_, v_h__2_172_, v_h__3_173_, v_h__4_174_, v_h__5_175_, v_h__6_176_, v_h__7_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter___boxed(lean_object* v_motive_179_, lean_object* v_op_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_, lean_object* v_h__3_183_, lean_object* v_h__4_184_, lean_object* v_h__5_185_, lean_object* v_h__6_186_, lean_object* v_h__7_187_){
_start:
{
uint8_t v_op_93__boxed_188_; lean_object* v_res_189_; 
v_op_93__boxed_188_ = lean_unbox(v_op_180_);
v_res_189_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr_0__Std_Tactic_BVDecide_BVExpr_bitblast_go_match__9_splitter(v_motive_179_, v_op_93__boxed_188_, v_h__1_181_, v_h__2_182_, v_h__3_183_, v_h__4_184_, v_h__5_185_, v_h__6_186_, v_h__7_187_);
return v_res_189_;
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
