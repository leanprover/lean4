// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend public import Std.Sat.AIG.If import Init.Omega
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(lean_object* v_w_1_, lean_object* v_aig_2_, lean_object* v_target_3_){
_start:
{
lean_object* v_start_4_; lean_object* v_x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_res_8_; lean_object* v_aig_9_; lean_object* v_vec_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_27_; 
v_start_4_ = lean_ctor_get(v_target_3_, 0);
v_x_5_ = lean_ctor_get(v_target_3_, 1);
v___x_6_ = lean_unsigned_to_nat(1u);
lean_inc(v_start_4_);
lean_inc_ref(v_x_5_);
lean_inc(v_w_1_);
v___x_7_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7_, 0, v_w_1_);
lean_ctor_set(v___x_7_, 1, v_x_5_);
lean_ctor_set(v___x_7_, 2, v_start_4_);
v_res_8_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v___x_6_, v_aig_2_, v___x_7_);
lean_dec_ref(v___x_7_);
v_aig_9_ = lean_ctor_get(v_res_8_, 0);
v_vec_10_ = lean_ctor_get(v_res_8_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_res_8_);
if (v_isSharedCheck_27_ == 0)
{
v___x_12_ = v_res_8_;
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_vec_10_);
lean_inc(v_aig_9_);
lean_dec(v_res_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_6_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_6_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_vec_10_);
v___x_15_ = v_reuseFailAlloc_26_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v_res_16_; lean_object* v_aig_17_; lean_object* v_vec_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
v_res_16_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_w_1_, v_aig_9_, v___x_15_);
lean_dec_ref(v___x_15_);
lean_dec(v_w_1_);
v_aig_17_ = lean_ctor_get(v_res_16_, 0);
v_vec_18_ = lean_ctor_get(v_res_16_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_res_16_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v_res_16_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_vec_18_);
lean_inc(v_aig_17_);
lean_dec(v_res_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_aig_17_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_vec_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg___boxed(lean_object* v_w_28_, lean_object* v_aig_29_, lean_object* v_target_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(v_w_28_, v_aig_29_, v_target_30_);
lean_dec_ref(v_target_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_w_35_, lean_object* v_aig_36_, lean_object* v_target_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(v_w_35_, v_aig_36_, v_target_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___boxed(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_w_42_, lean_object* v_aig_43_, lean_object* v_target_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(v_00_u03b1_39_, v_inst_40_, v_inst_41_, v_w_42_, v_aig_43_, v_target_44_);
lean_dec_ref(v_target_44_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_inst_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(lean_object* v_aig_46_, lean_object* v_w_47_, lean_object* v_idx_48_, lean_object* v_x_49_, lean_object* v_acc_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_nat_dec_lt(v_idx_48_, v_w_47_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec_ref(v_x_49_);
lean_dec(v_idx_48_);
lean_dec(v_w_47_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_aig_46_);
lean_ctor_set(v___x_52_, 1, v_acc_50_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v_res_54_; lean_object* v_aig_55_; lean_object* v_vec_56_; lean_object* v_acc_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc_ref(v_x_49_);
lean_inc(v_idx_48_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v_idx_48_);
lean_ctor_set(v___x_53_, 1, v_x_49_);
lean_inc(v_w_47_);
v_res_54_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(v_w_47_, v_aig_46_, v___x_53_);
lean_dec_ref(v___x_53_);
v_aig_55_ = lean_ctor_get(v_res_54_, 0);
lean_inc_ref(v_aig_55_);
v_vec_56_ = lean_ctor_get(v_res_54_, 1);
lean_inc_ref(v_vec_56_);
lean_dec_ref(v_res_54_);
v_acc_57_ = l_Array_append___redArg(v_acc_50_, v_vec_56_);
lean_dec_ref(v_vec_56_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_idx_48_, v___x_58_);
lean_dec(v_idx_48_);
v_aig_46_ = v_aig_55_;
v_idx_48_ = v___x_59_;
v_acc_50_ = v_acc_57_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_outWidth_64_, lean_object* v_aig_65_, lean_object* v_w_66_, lean_object* v_idx_67_, lean_object* v_x_68_, lean_object* v_acc_69_, lean_object* v_h_70_, lean_object* v_h_x27_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(v_aig_65_, v_w_66_, v_idx_67_, v_x_68_, v_acc_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___boxed(lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_outWidth_76_, lean_object* v_aig_77_, lean_object* v_w_78_, lean_object* v_idx_79_, lean_object* v_x_80_, lean_object* v_acc_81_, lean_object* v_h_82_, lean_object* v_h_x27_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(v_00_u03b1_73_, v_inst_74_, v_inst_75_, v_outWidth_76_, v_aig_77_, v_w_78_, v_idx_79_, v_x_80_, v_acc_81_, v_h_82_, v_h_x27_83_);
lean_dec(v_outWidth_76_);
lean_dec_ref(v_inst_75_);
lean_dec_ref(v_inst_74_);
return v_res_84_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_BitVec_ofNat(v___x_85_, v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_initAcc_89_; 
v___x_87_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0);
v___x_88_ = lean_unsigned_to_nat(0u);
v_initAcc_89_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v___x_88_, v___x_87_);
return v_initAcc_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(lean_object* v_aig_90_, lean_object* v_target_91_){
_start:
{
lean_object* v_w_92_; lean_object* v_x_93_; lean_object* v___x_94_; lean_object* v_initAcc_95_; lean_object* v___x_96_; 
v_w_92_ = lean_ctor_get(v_target_91_, 0);
lean_inc(v_w_92_);
v_x_93_ = lean_ctor_get(v_target_91_, 1);
lean_inc_ref(v_x_93_);
lean_dec_ref(v_target_91_);
v___x_94_ = lean_unsigned_to_nat(0u);
v_initAcc_95_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1);
v___x_96_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(v_aig_90_, v_w_92_, v___x_94_, v_x_93_, v_initAcc_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_outWidth_100_, lean_object* v_aig_101_, lean_object* v_target_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(v_aig_101_, v_target_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___boxed(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_outWidth_107_, lean_object* v_aig_108_, lean_object* v_target_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(v_00_u03b1_104_, v_inst_105_, v_inst_106_, v_outWidth_107_, v_aig_108_, v_target_109_);
lean_dec(v_outWidth_107_);
lean_dec_ref(v_inst_106_);
lean_dec_ref(v_inst_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_aig_113_, lean_object* v_w_114_, lean_object* v_len_115_, lean_object* v_iterNum_116_, lean_object* v_oldLayer_117_, lean_object* v_newLayer_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v_iterNum_116_, v___x_120_);
v___x_122_ = lean_nat_sub(v_len_115_, v___x_121_);
lean_dec(v___x_121_);
v___x_123_ = lean_nat_dec_lt(v___x_119_, v___x_122_);
lean_dec(v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v_oldLayer_117_);
lean_dec(v_iterNum_116_);
lean_dec(v_w_114_);
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_111_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_aig_113_);
lean_ctor_set(v___x_124_, 1, v_newLayer_118_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_res_129_; lean_object* v_aig_130_; lean_object* v_vec_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_res_136_; lean_object* v_aig_137_; lean_object* v_vec_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_155_; 
v___x_125_ = lean_nat_mul(v_len_115_, v_w_114_);
v___x_126_ = lean_nat_mul(v___x_120_, v_iterNum_116_);
v___x_127_ = lean_nat_mul(v___x_126_, v_w_114_);
lean_inc_ref(v_oldLayer_117_);
lean_inc(v___x_125_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_125_);
lean_ctor_set(v___x_128_, 1, v_oldLayer_117_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
v_res_129_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_w_114_, v_aig_113_, v___x_128_);
lean_dec_ref(v___x_128_);
v_aig_130_ = lean_ctor_get(v_res_129_, 0);
lean_inc_ref(v_aig_130_);
v_vec_131_ = lean_ctor_get(v_res_129_, 1);
lean_inc_ref(v_vec_131_);
lean_dec_ref(v_res_129_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v___x_126_, v___x_132_);
lean_dec(v___x_126_);
v___x_134_ = lean_nat_mul(v___x_133_, v_w_114_);
lean_dec(v___x_133_);
lean_inc_ref(v_oldLayer_117_);
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_125_);
lean_ctor_set(v___x_135_, 1, v_oldLayer_117_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
v_res_136_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_w_114_, v_aig_130_, v___x_135_);
lean_dec_ref(v___x_135_);
v_aig_137_ = lean_ctor_get(v_res_136_, 0);
v_vec_138_ = lean_ctor_get(v_res_136_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_res_136_);
if (v_isSharedCheck_155_ == 0)
{
v___x_140_ = v_res_136_;
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vec_138_);
lean_inc(v_aig_137_);
lean_dec(v_res_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v_vec_131_);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_vec_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_vec_138_);
v___x_143_ = v_reuseFailAlloc_154_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_res_144_; lean_object* v_aig_145_; lean_object* v_vec_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_res_149_; lean_object* v_aig_150_; lean_object* v_vec_151_; lean_object* v___x_152_; 
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v_res_144_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_111_, v_inst_112_, v_w_114_, v_aig_137_, v___x_143_);
v_aig_145_ = lean_ctor_get(v_res_144_, 0);
lean_inc_ref(v_aig_145_);
v_vec_146_ = lean_ctor_get(v_res_144_, 1);
lean_inc_ref(v_vec_146_);
lean_dec_ref(v_res_144_);
v___x_147_ = lean_nat_mul(v_iterNum_116_, v_w_114_);
lean_inc(v_w_114_);
v___x_148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_148_, 0, v_w_114_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
lean_ctor_set(v___x_148_, 2, v_vec_146_);
lean_ctor_set(v___x_148_, 3, v_newLayer_118_);
v_res_149_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(v_aig_145_, v___x_148_);
v_aig_150_ = lean_ctor_get(v_res_149_, 0);
lean_inc_ref(v_aig_150_);
v_vec_151_ = lean_ctor_get(v_res_149_, 1);
lean_inc_ref(v_vec_151_);
lean_dec_ref(v_res_149_);
v___x_152_ = lean_nat_add(v_iterNum_116_, v___x_132_);
lean_dec(v_iterNum_116_);
v_aig_113_ = v_aig_150_;
v_iterNum_116_ = v___x_152_;
v_newLayer_118_ = v_vec_151_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg___boxed(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_aig_158_, lean_object* v_w_159_, lean_object* v_len_160_, lean_object* v_iterNum_161_, lean_object* v_oldLayer_162_, lean_object* v_newLayer_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_156_, v_inst_157_, v_aig_158_, v_w_159_, v_len_160_, v_iterNum_161_, v_oldLayer_162_, v_newLayer_163_);
lean_dec(v_len_160_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_outWidth_168_, lean_object* v_aig_169_, lean_object* v_w_170_, lean_object* v_len_171_, lean_object* v_iterNum_172_, lean_object* v_oldLayer_173_, lean_object* v_newLayer_174_, lean_object* v_hold_175_, lean_object* v_hout_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_166_, v_inst_167_, v_aig_169_, v_w_170_, v_len_171_, v_iterNum_172_, v_oldLayer_173_, v_newLayer_174_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___boxed(lean_object* v_00_u03b1_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_outWidth_181_, lean_object* v_aig_182_, lean_object* v_w_183_, lean_object* v_len_184_, lean_object* v_iterNum_185_, lean_object* v_oldLayer_186_, lean_object* v_newLayer_187_, lean_object* v_hold_188_, lean_object* v_hout_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(v_00_u03b1_178_, v_inst_179_, v_inst_180_, v_outWidth_181_, v_aig_182_, v_w_183_, v_len_184_, v_iterNum_185_, v_oldLayer_186_, v_newLayer_187_, v_hold_188_, v_hout_189_);
lean_dec(v_len_184_);
lean_dec(v_outWidth_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_aig_193_, lean_object* v_target_194_){
_start:
{
lean_object* v_w_195_; lean_object* v_len_196_; lean_object* v_oldLayer_197_; lean_object* v___x_198_; lean_object* v_initAcc_199_; lean_object* v___x_200_; 
v_w_195_ = lean_ctor_get(v_target_194_, 0);
lean_inc(v_w_195_);
v_len_196_ = lean_ctor_get(v_target_194_, 1);
lean_inc(v_len_196_);
v_oldLayer_197_ = lean_ctor_get(v_target_194_, 2);
lean_inc_ref(v_oldLayer_197_);
lean_dec_ref(v_target_194_);
v___x_198_ = lean_unsigned_to_nat(0u);
v_initAcc_199_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1);
v___x_200_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_191_, v_inst_192_, v_aig_193_, v_w_195_, v_len_196_, v___x_198_, v_oldLayer_197_, v_initAcc_199_);
lean_dec(v_len_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(lean_object* v_00_u03b1_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_outWidth_204_, lean_object* v_aig_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(v_inst_202_, v_inst_203_, v_aig_205_, v_target_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___boxed(lean_object* v_00_u03b1_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_outWidth_211_, lean_object* v_aig_212_, lean_object* v_target_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(v_00_u03b1_208_, v_inst_209_, v_inst_210_, v_outWidth_211_, v_aig_212_, v_target_213_);
lean_dec(v_outWidth_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_w_217_, lean_object* v_aig_218_, lean_object* v_len_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_dec_lt(v___x_221_, v_len_219_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v_len_219_);
lean_dec(v_w_217_);
lean_dec_ref(v_inst_216_);
lean_dec_ref(v_inst_215_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_aig_218_);
lean_ctor_set(v___x_223_, 1, v_x_220_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_res_226_; lean_object* v_aig_227_; lean_object* v_vec_228_; lean_object* v___x_229_; 
v___x_224_ = lean_nat_add(v_len_219_, v___x_221_);
lean_inc(v_w_217_);
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v_w_217_);
lean_ctor_set(v___x_225_, 1, v_len_219_);
lean_ctor_set(v___x_225_, 2, v_x_220_);
lean_inc_ref(v_inst_216_);
lean_inc_ref(v_inst_215_);
v_res_226_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(v_inst_215_, v_inst_216_, v_aig_218_, v___x_225_);
v_aig_227_ = lean_ctor_get(v_res_226_, 0);
lean_inc_ref(v_aig_227_);
v_vec_228_ = lean_ctor_get(v_res_226_, 1);
lean_inc_ref(v_vec_228_);
lean_dec_ref(v_res_226_);
v___x_229_ = lean_nat_shiftr(v___x_224_, v___x_221_);
lean_dec(v___x_224_);
v_aig_218_ = v_aig_227_;
v_len_219_ = v___x_229_;
v_x_220_ = v_vec_228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_w_234_, lean_object* v_aig_235_, lean_object* v_len_236_, lean_object* v_x_237_, lean_object* v_h_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(v_inst_232_, v_inst_233_, v_w_234_, v_aig_235_, v_len_236_, v_x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_w_242_, lean_object* v_aig_243_, lean_object* v_target_244_){
_start:
{
lean_object* v_len_245_; lean_object* v_x_246_; lean_object* v___x_247_; 
v_len_245_ = lean_ctor_get(v_target_244_, 0);
lean_inc(v_len_245_);
v_x_246_ = lean_ctor_get(v_target_244_, 1);
lean_inc_ref(v_x_246_);
lean_dec_ref(v_target_244_);
v___x_247_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(v_inst_240_, v_inst_241_, v_w_242_, v_aig_243_, v_len_245_, v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_w_251_, lean_object* v_aig_252_, lean_object* v_target_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(v_inst_249_, v_inst_250_, v_w_251_, v_aig_252_, v_target_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_w_257_, lean_object* v_aig_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_dec_lt(v___x_260_, v_w_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
lean_dec_ref(v_inst_256_);
lean_dec_ref(v_inst_255_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_lt(v___x_262_, v_w_257_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v_zero_265_; lean_object* v___x_266_; 
lean_dec_ref(v_x_259_);
v___x_264_ = l_BitVec_ofNat(v_w_257_, v___x_262_);
v_zero_265_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_257_, v___x_264_);
lean_dec(v___x_264_);
lean_dec(v_w_257_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_aig_258_);
lean_ctor_set(v___x_266_, 1, v_zero_265_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v_w_257_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_aig_258_);
lean_ctor_set(v___x_267_, 1, v_x_259_);
return v___x_267_;
}
}
else
{
lean_object* v___x_268_; lean_object* v_res_269_; lean_object* v_aig_270_; lean_object* v_vec_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
lean_inc(v_w_257_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_w_257_);
lean_ctor_set(v___x_268_, 1, v_x_259_);
v_res_269_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(v_aig_258_, v___x_268_);
v_aig_270_ = lean_ctor_get(v_res_269_, 0);
v_vec_271_ = lean_ctor_get(v_res_269_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_res_269_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v_res_269_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_vec_271_);
lean_inc(v_aig_270_);
lean_dec(v_res_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
lean_inc(v_w_257_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_w_257_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_w_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_vec_271_);
v___x_276_ = v_reuseFailAlloc_278_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(v_inst_255_, v_inst_256_, v_w_257_, v_aig_270_, v___x_276_);
return v___x_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_w_283_, lean_object* v_aig_284_, lean_object* v_x_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(v_inst_281_, v_inst_282_, v_w_283_, v_aig_284_, v_x_285_);
return v___x_286_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
}
#ifdef __cplusplus
}
#endif
