// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(lean_object* v_w_1_, lean_object* v_input_2_, lean_object* v_distance_3_, lean_object* v_curr_4_, lean_object* v_s_5_){
_start:
{
lean_object* v_gate_7_; uint8_t v_invert_8_; lean_object* v_gate_18_; uint8_t v_invert_19_; uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_lt(v_curr_4_, v_w_1_);
if (v___x_28_ == 0)
{
lean_dec(v_curr_4_);
return v_s_5_;
}
else
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_nat_mod(v_distance_3_, v_w_1_);
v___x_30_ = lean_nat_dec_lt(v_curr_4_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_31_ = lean_nat_sub(v_curr_4_, v___x_29_);
lean_dec(v___x_29_);
v_ref_32_ = lean_array_fget_borrowed(v_input_2_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_shiftr(v_ref_32_, v___x_33_);
v___x_35_ = lean_nat_land(v___x_33_, v_ref_32_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
if (v___x_37_ == 0)
{
v_gate_7_ = v___x_34_;
v_invert_8_ = v___x_28_;
goto v___jp_6_;
}
else
{
v_gate_7_ = v___x_34_;
v_invert_8_ = v___x_30_;
goto v___jp_6_;
}
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_ref_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_38_ = lean_nat_sub(v_w_1_, v___x_29_);
lean_dec(v___x_29_);
v___x_39_ = lean_nat_add(v___x_38_, v_curr_4_);
lean_dec(v___x_38_);
v_ref_40_ = lean_array_fget_borrowed(v_input_2_, v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_shiftr(v_ref_40_, v___x_41_);
v___x_43_ = lean_nat_land(v___x_41_, v_ref_40_);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_43_);
if (v___x_45_ == 0)
{
v_gate_18_ = v___x_42_;
v_invert_19_ = v___x_30_;
goto v___jp_17_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
v_gate_18_ = v___x_42_;
v_invert_19_ = v___x_46_;
goto v___jp_17_;
}
}
}
v___jp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_s_15_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v_curr_4_, v___x_9_);
lean_dec(v_curr_4_);
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_nat_mul(v_gate_7_, v___x_11_);
lean_dec(v_gate_7_);
v___x_13_ = l_Bool_toNat(v_invert_8_);
v___x_14_ = lean_nat_lor(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_12_);
v_s_15_ = lean_array_push(v_s_5_, v___x_14_);
v_curr_4_ = v___x_10_;
v_s_5_ = v_s_15_;
goto _start;
}
v___jp_17_:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_s_26_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_nat_add(v_curr_4_, v___x_20_);
lean_dec(v_curr_4_);
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = lean_nat_mul(v_gate_18_, v___x_22_);
lean_dec(v_gate_18_);
v___x_24_ = l_Bool_toNat(v_invert_19_);
v___x_25_ = lean_nat_lor(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
v_s_26_ = lean_array_push(v_s_5_, v___x_25_);
v_curr_4_ = v___x_21_;
v_s_5_ = v_s_26_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg___boxed(lean_object* v_w_47_, lean_object* v_input_48_, lean_object* v_distance_49_, lean_object* v_curr_50_, lean_object* v_s_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_47_, v_input_48_, v_distance_49_, v_curr_50_, v_s_51_);
lean_dec(v_distance_49_);
lean_dec_ref(v_input_48_);
lean_dec(v_w_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_w_56_, lean_object* v_aig_57_, lean_object* v_input_58_, lean_object* v_distance_59_, lean_object* v_curr_60_, lean_object* v_hcurr_61_, lean_object* v_s_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_56_, v_input_58_, v_distance_59_, v_curr_60_, v_s_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___boxed(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_aig_68_, lean_object* v_input_69_, lean_object* v_distance_70_, lean_object* v_curr_71_, lean_object* v_hcurr_72_, lean_object* v_s_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(v_00_u03b1_64_, v_inst_65_, v_inst_66_, v_w_67_, v_aig_68_, v_input_69_, v_distance_70_, v_curr_71_, v_hcurr_72_, v_s_73_);
lean_dec(v_distance_70_);
lean_dec_ref(v_input_69_);
lean_dec_ref(v_aig_68_);
lean_dec(v_w_67_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(lean_object* v_w_75_, lean_object* v_aig_76_, lean_object* v_target_77_){
_start:
{
lean_object* v_vec_78_; lean_object* v_distance_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_89_; 
v_vec_78_ = lean_ctor_get(v_target_77_, 0);
v_distance_79_ = lean_ctor_get(v_target_77_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_target_77_);
if (v_isSharedCheck_89_ == 0)
{
v___x_81_ = v_target_77_;
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_distance_79_);
lean_inc(v_vec_78_);
lean_dec(v_target_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_mk_empty_array_with_capacity(v_w_75_);
v___x_85_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(v_w_75_, v_vec_78_, v_distance_79_, v___x_83_, v___x_84_);
lean_dec(v_distance_79_);
lean_dec_ref(v_vec_78_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_85_);
lean_ctor_set(v___x_81_, 0, v_aig_76_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_aig_76_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg___boxed(lean_object* v_w_90_, lean_object* v_aig_91_, lean_object* v_target_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(v_w_90_, v_aig_91_, v_target_92_);
lean_dec(v_w_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_w_97_, lean_object* v_aig_98_, lean_object* v_target_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(v_w_97_, v_aig_98_, v_target_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___boxed(lean_object* v_00_u03b1_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_w_104_, lean_object* v_aig_105_, lean_object* v_target_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(v_00_u03b1_101_, v_inst_102_, v_inst_103_, v_w_104_, v_aig_105_, v_target_106_);
lean_dec(v_w_104_);
lean_dec_ref(v_inst_103_);
lean_dec_ref(v_inst_102_);
return v_res_107_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin);
}
#ifdef __cplusplus
}
#endif
