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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_7_, 3);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter___redArg(lean_object* v_target_46_, lean_object* v_h__1_47_){
_start:
{
lean_object* v_start_48_; lean_object* v_x_49_; lean_object* v___x_50_; 
v_start_48_ = lean_ctor_get(v_target_46_, 0);
lean_inc(v_start_48_);
v_x_49_ = lean_ctor_get(v_target_46_, 1);
lean_inc_ref(v_x_49_);
lean_dec_ref(v_target_46_);
v___x_50_ = lean_apply_2(v_h__1_47_, v_start_48_, v_x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_w_54_, lean_object* v_aig_55_, lean_object* v_motive_56_, lean_object* v_target_57_, lean_object* v_h__1_58_){
_start:
{
lean_object* v_start_59_; lean_object* v_x_60_; lean_object* v___x_61_; 
v_start_59_ = lean_ctor_get(v_target_57_, 0);
lean_inc(v_start_59_);
v_x_60_ = lean_ctor_get(v_target_57_, 1);
lean_inc_ref(v_x_60_);
lean_dec_ref(v_target_57_);
v___x_61_ = lean_apply_2(v_h__1_58_, v_start_59_, v_x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter___boxed(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_w_65_, lean_object* v_aig_66_, lean_object* v_motive_67_, lean_object* v_target_68_, lean_object* v_h__1_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit_match__1_splitter(v_00_u03b1_62_, v_inst_63_, v_inst_64_, v_w_65_, v_aig_66_, v_motive_67_, v_target_68_, v_h__1_69_);
lean_dec_ref(v_aig_66_);
lean_dec(v_w_65_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(lean_object* v_aig_71_, lean_object* v_w_72_, lean_object* v_idx_73_, lean_object* v_x_74_, lean_object* v_acc_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_nat_dec_lt(v_idx_73_, v_w_72_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v_x_74_);
lean_dec(v_idx_73_);
lean_dec(v_w_72_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_aig_71_);
lean_ctor_set(v___x_77_, 1, v_acc_75_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v_res_79_; lean_object* v_aig_80_; lean_object* v_vec_81_; lean_object* v_acc_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_inc_ref(v_x_74_);
lean_inc(v_idx_73_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_idx_73_);
lean_ctor_set(v___x_78_, 1, v_x_74_);
lean_inc(v_w_72_);
v_res_79_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(v_w_72_, v_aig_71_, v___x_78_);
lean_dec_ref_known(v___x_78_, 2);
v_aig_80_ = lean_ctor_get(v_res_79_, 0);
lean_inc_ref(v_aig_80_);
v_vec_81_ = lean_ctor_get(v_res_79_, 1);
lean_inc_ref(v_vec_81_);
lean_dec_ref(v_res_79_);
v_acc_82_ = l_Array_append___redArg(v_acc_75_, v_vec_81_);
lean_dec_ref(v_vec_81_);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_add(v_idx_73_, v___x_83_);
lean_dec(v_idx_73_);
v_aig_71_ = v_aig_80_;
v_idx_73_ = v___x_84_;
v_acc_75_ = v_acc_82_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_outWidth_89_, lean_object* v_aig_90_, lean_object* v_w_91_, lean_object* v_idx_92_, lean_object* v_x_93_, lean_object* v_acc_94_, lean_object* v_h_95_, lean_object* v_h_x27_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(v_aig_90_, v_w_91_, v_idx_92_, v_x_93_, v_acc_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___boxed(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_outWidth_101_, lean_object* v_aig_102_, lean_object* v_w_103_, lean_object* v_idx_104_, lean_object* v_x_105_, lean_object* v_acc_106_, lean_object* v_h_107_, lean_object* v_h_x27_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(v_00_u03b1_98_, v_inst_99_, v_inst_100_, v_outWidth_101_, v_aig_102_, v_w_103_, v_idx_104_, v_x_105_, v_acc_106_, v_h_107_, v_h_x27_108_);
lean_dec(v_outWidth_101_);
lean_dec_ref(v_inst_100_);
lean_dec_ref(v_inst_99_);
return v_res_109_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_BitVec_ofNat(v___x_110_, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_initAcc_114_; 
v___x_112_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0);
v___x_113_ = lean_unsigned_to_nat(0u);
v_initAcc_114_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v___x_113_, v___x_112_);
return v_initAcc_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(lean_object* v_aig_115_, lean_object* v_target_116_){
_start:
{
lean_object* v_w_117_; lean_object* v_x_118_; lean_object* v___x_119_; lean_object* v_initAcc_120_; lean_object* v___x_121_; 
v_w_117_ = lean_ctor_get(v_target_116_, 0);
lean_inc(v_w_117_);
v_x_118_ = lean_ctor_get(v_target_116_, 1);
lean_inc_ref(v_x_118_);
lean_dec_ref(v_target_116_);
v___x_119_ = lean_unsigned_to_nat(0u);
v_initAcc_120_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1);
v___x_121_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(v_aig_115_, v_w_117_, v___x_119_, v_x_118_, v_initAcc_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_outWidth_125_, lean_object* v_aig_126_, lean_object* v_target_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(v_aig_126_, v_target_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___boxed(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_outWidth_132_, lean_object* v_aig_133_, lean_object* v_target_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(v_00_u03b1_129_, v_inst_130_, v_inst_131_, v_outWidth_132_, v_aig_133_, v_target_134_);
lean_dec(v_outWidth_132_);
lean_dec_ref(v_inst_131_);
lean_dec_ref(v_inst_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_aig_138_, lean_object* v_w_139_, lean_object* v_len_140_, lean_object* v_iterNum_141_, lean_object* v_oldLayer_142_, lean_object* v_newLayer_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_unsigned_to_nat(2u);
v___x_146_ = lean_nat_mul(v_iterNum_141_, v___x_145_);
v___x_147_ = lean_nat_sub(v_len_140_, v___x_146_);
lean_dec(v___x_146_);
v___x_148_ = lean_nat_dec_lt(v___x_144_, v___x_147_);
lean_dec(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec_ref(v_oldLayer_142_);
lean_dec(v_iterNum_141_);
lean_dec(v_w_139_);
lean_dec_ref(v_inst_137_);
lean_dec_ref(v_inst_136_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_aig_138_);
lean_ctor_set(v___x_149_, 1, v_newLayer_143_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_res_154_; lean_object* v_aig_155_; lean_object* v_vec_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_res_161_; lean_object* v_aig_162_; lean_object* v_vec_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_180_; 
v___x_150_ = lean_nat_mul(v_len_140_, v_w_139_);
v___x_151_ = lean_nat_mul(v___x_145_, v_iterNum_141_);
v___x_152_ = lean_nat_mul(v___x_151_, v_w_139_);
lean_inc_ref_n(v_oldLayer_142_, 2);
lean_inc(v___x_150_);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_150_);
lean_ctor_set(v___x_153_, 1, v_oldLayer_142_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
v_res_154_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_w_139_, v_aig_138_, v___x_153_);
lean_dec_ref_known(v___x_153_, 3);
v_aig_155_ = lean_ctor_get(v_res_154_, 0);
lean_inc_ref(v_aig_155_);
v_vec_156_ = lean_ctor_get(v_res_154_, 1);
lean_inc_ref(v_vec_156_);
lean_dec_ref(v_res_154_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v___x_151_, v___x_157_);
lean_dec(v___x_151_);
v___x_159_ = lean_nat_mul(v___x_158_, v_w_139_);
lean_dec(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_150_);
lean_ctor_set(v___x_160_, 1, v_oldLayer_142_);
lean_ctor_set(v___x_160_, 2, v___x_159_);
v_res_161_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_w_139_, v_aig_155_, v___x_160_);
lean_dec_ref_known(v___x_160_, 3);
v_aig_162_ = lean_ctor_get(v_res_161_, 0);
v_vec_163_ = lean_ctor_get(v_res_161_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_res_161_);
if (v_isSharedCheck_180_ == 0)
{
v___x_165_ = v_res_161_;
v_isShared_166_ = v_isSharedCheck_180_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_vec_163_);
lean_inc(v_aig_162_);
lean_dec(v_res_161_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_180_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v_vec_156_);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_vec_156_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_vec_163_);
v___x_168_ = v_reuseFailAlloc_179_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v_res_169_; lean_object* v_aig_170_; lean_object* v_vec_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_res_174_; lean_object* v_aig_175_; lean_object* v_vec_176_; lean_object* v___x_177_; 
lean_inc_ref(v_inst_137_);
lean_inc_ref(v_inst_136_);
v_res_169_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_136_, v_inst_137_, v_w_139_, v_aig_162_, v___x_168_);
v_aig_170_ = lean_ctor_get(v_res_169_, 0);
lean_inc_ref(v_aig_170_);
v_vec_171_ = lean_ctor_get(v_res_169_, 1);
lean_inc_ref(v_vec_171_);
lean_dec_ref(v_res_169_);
v___x_172_ = lean_nat_mul(v_iterNum_141_, v_w_139_);
lean_inc(v_w_139_);
v___x_173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_173_, 0, v_w_139_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set(v___x_173_, 2, v_vec_171_);
lean_ctor_set(v___x_173_, 3, v_newLayer_143_);
v_res_174_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(v_aig_170_, v___x_173_);
v_aig_175_ = lean_ctor_get(v_res_174_, 0);
lean_inc_ref(v_aig_175_);
v_vec_176_ = lean_ctor_get(v_res_174_, 1);
lean_inc_ref(v_vec_176_);
lean_dec_ref(v_res_174_);
v___x_177_ = lean_nat_add(v_iterNum_141_, v___x_157_);
lean_dec(v_iterNum_141_);
v_aig_138_ = v_aig_175_;
v_iterNum_141_ = v___x_177_;
v_newLayer_143_ = v_vec_176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg___boxed(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_aig_183_, lean_object* v_w_184_, lean_object* v_len_185_, lean_object* v_iterNum_186_, lean_object* v_oldLayer_187_, lean_object* v_newLayer_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_181_, v_inst_182_, v_aig_183_, v_w_184_, v_len_185_, v_iterNum_186_, v_oldLayer_187_, v_newLayer_188_);
lean_dec(v_len_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_outWidth_193_, lean_object* v_aig_194_, lean_object* v_w_195_, lean_object* v_len_196_, lean_object* v_iterNum_197_, lean_object* v_oldLayer_198_, lean_object* v_newLayer_199_, lean_object* v_hold_200_, lean_object* v_hout_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_191_, v_inst_192_, v_aig_194_, v_w_195_, v_len_196_, v_iterNum_197_, v_oldLayer_198_, v_newLayer_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___boxed(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_outWidth_206_, lean_object* v_aig_207_, lean_object* v_w_208_, lean_object* v_len_209_, lean_object* v_iterNum_210_, lean_object* v_oldLayer_211_, lean_object* v_newLayer_212_, lean_object* v_hold_213_, lean_object* v_hout_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(v_00_u03b1_203_, v_inst_204_, v_inst_205_, v_outWidth_206_, v_aig_207_, v_w_208_, v_len_209_, v_iterNum_210_, v_oldLayer_211_, v_newLayer_212_, v_hold_213_, v_hout_214_);
lean_dec(v_len_209_);
lean_dec(v_outWidth_206_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_aig_218_, lean_object* v_target_219_){
_start:
{
lean_object* v_w_220_; lean_object* v_len_221_; lean_object* v_oldLayer_222_; lean_object* v___x_223_; lean_object* v_initAcc_224_; lean_object* v___x_225_; 
v_w_220_ = lean_ctor_get(v_target_219_, 0);
lean_inc(v_w_220_);
v_len_221_ = lean_ctor_get(v_target_219_, 1);
lean_inc(v_len_221_);
v_oldLayer_222_ = lean_ctor_get(v_target_219_, 2);
lean_inc_ref(v_oldLayer_222_);
lean_dec_ref(v_target_219_);
v___x_223_ = lean_unsigned_to_nat(0u);
v_initAcc_224_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1);
v___x_225_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(v_inst_216_, v_inst_217_, v_aig_218_, v_w_220_, v_len_221_, v___x_223_, v_oldLayer_222_, v_initAcc_224_);
lean_dec(v_len_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_outWidth_229_, lean_object* v_aig_230_, lean_object* v_target_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(v_inst_227_, v_inst_228_, v_aig_230_, v_target_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___boxed(lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_outWidth_236_, lean_object* v_aig_237_, lean_object* v_target_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(v_00_u03b1_233_, v_inst_234_, v_inst_235_, v_outWidth_236_, v_aig_237_, v_target_238_);
lean_dec(v_outWidth_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_w_242_, lean_object* v_aig_243_, lean_object* v_len_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_dec_lt(v___x_246_, v_len_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_len_244_);
lean_dec(v_w_242_);
lean_dec_ref(v_inst_241_);
lean_dec_ref(v_inst_240_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_aig_243_);
lean_ctor_set(v___x_248_, 1, v_x_245_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_res_251_; lean_object* v_aig_252_; lean_object* v_vec_253_; lean_object* v___x_254_; 
v___x_249_ = lean_nat_add(v_len_244_, v___x_246_);
lean_inc(v_w_242_);
v___x_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_250_, 0, v_w_242_);
lean_ctor_set(v___x_250_, 1, v_len_244_);
lean_ctor_set(v___x_250_, 2, v_x_245_);
lean_inc_ref(v_inst_241_);
lean_inc_ref(v_inst_240_);
v_res_251_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(v_inst_240_, v_inst_241_, v_aig_243_, v___x_250_);
v_aig_252_ = lean_ctor_get(v_res_251_, 0);
lean_inc_ref(v_aig_252_);
v_vec_253_ = lean_ctor_get(v_res_251_, 1);
lean_inc_ref(v_vec_253_);
lean_dec_ref(v_res_251_);
v___x_254_ = lean_nat_shiftr(v___x_249_, v___x_246_);
lean_dec(v___x_249_);
v_aig_243_ = v_aig_252_;
v_len_244_ = v___x_254_;
v_x_245_ = v_vec_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go(lean_object* v_00_u03b1_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_w_259_, lean_object* v_aig_260_, lean_object* v_len_261_, lean_object* v_x_262_, lean_object* v_h_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(v_inst_257_, v_inst_258_, v_w_259_, v_aig_260_, v_len_261_, v_x_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_w_267_, lean_object* v_aig_268_, lean_object* v_target_269_){
_start:
{
lean_object* v_len_270_; lean_object* v_x_271_; lean_object* v___x_272_; 
v_len_270_ = lean_ctor_get(v_target_269_, 0);
lean_inc(v_len_270_);
v_x_271_ = lean_ctor_get(v_target_269_, 1);
lean_inc_ref(v_x_271_);
lean_dec_ref(v_target_269_);
v___x_272_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(v_inst_265_, v_inst_266_, v_w_267_, v_aig_268_, v_len_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_w_276_, lean_object* v_aig_277_, lean_object* v_target_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(v_inst_274_, v_inst_275_, v_w_276_, v_aig_277_, v_target_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_w_282_, lean_object* v_aig_283_, lean_object* v_x_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_dec_lt(v___x_285_, v_w_282_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_lt(v___x_287_, v_w_282_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v_zero_290_; lean_object* v___x_291_; 
lean_dec_ref(v_x_284_);
v___x_289_ = l_BitVec_ofNat(v_w_282_, v___x_287_);
v_zero_290_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_282_, v___x_289_);
lean_dec(v___x_289_);
lean_dec(v_w_282_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_aig_283_);
lean_ctor_set(v___x_291_, 1, v_zero_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_dec(v_w_282_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_aig_283_);
lean_ctor_set(v___x_292_, 1, v_x_284_);
return v___x_292_;
}
}
else
{
lean_object* v___x_293_; lean_object* v_res_294_; lean_object* v_aig_295_; lean_object* v_vec_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
lean_inc(v_w_282_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_w_282_);
lean_ctor_set(v___x_293_, 1, v_x_284_);
v_res_294_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(v_aig_283_, v___x_293_);
v_aig_295_ = lean_ctor_get(v_res_294_, 0);
v_vec_296_ = lean_ctor_get(v_res_294_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_res_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v_res_294_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_vec_296_);
lean_inc(v_aig_295_);
lean_dec(v_res_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
lean_inc(v_w_282_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_w_282_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_w_282_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_vec_296_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(v_inst_280_, v_inst_281_, v_w_282_, v_aig_295_, v___x_301_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop(lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_w_308_, lean_object* v_aig_309_, lean_object* v_x_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(v_inst_306_, v_inst_307_, v_w_308_, v_aig_309_, v_x_310_);
return v___x_311_;
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
