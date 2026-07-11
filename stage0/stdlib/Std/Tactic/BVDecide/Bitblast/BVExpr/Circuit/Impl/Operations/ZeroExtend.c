// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(lean_object* v_aig_1_, lean_object* v_w_2_, lean_object* v_input_3_, lean_object* v_newWidth_4_, lean_object* v_curr_5_, lean_object* v_s_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_curr_5_, v_newWidth_4_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v_curr_5_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_aig_1_);
lean_ctor_set(v___x_8_, 1, v_s_6_);
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_curr_5_, v_w_2_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_s_13_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_curr_5_, v___x_10_);
lean_dec(v_curr_5_);
v___x_12_ = lean_bool_to_nat(v___x_9_);
v_s_13_ = lean_array_push(v_s_6_, v___x_12_);
v_curr_5_ = v___x_11_;
v_s_6_ = v_s_13_;
goto _start;
}
else
{
lean_object* v_ref_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_s_27_; 
v_ref_15_ = lean_array_fget_borrowed(v_input_3_, v_curr_5_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_land(v___x_16_, v_ref_15_);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_dec_eq(v___x_17_, v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_nat_shiftr(v_ref_15_, v___x_16_);
v___x_21_ = lean_bool_not(v___x_19_);
v___x_22_ = lean_nat_add(v_curr_5_, v___x_16_);
lean_dec(v_curr_5_);
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_nat_mul(v___x_20_, v___x_23_);
lean_dec(v___x_20_);
v___x_25_ = lean_bool_to_nat(v___x_21_);
v___x_26_ = lean_nat_lor(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
v_s_27_ = lean_array_push(v_s_6_, v___x_26_);
v_curr_5_ = v___x_22_;
v_s_6_ = v_s_27_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg___boxed(lean_object* v_aig_29_, lean_object* v_w_30_, lean_object* v_input_31_, lean_object* v_newWidth_32_, lean_object* v_curr_33_, lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_29_, v_w_30_, v_input_31_, v_newWidth_32_, v_curr_33_, v_s_34_);
lean_dec(v_newWidth_32_);
lean_dec_ref(v_input_31_);
lean_dec(v_w_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_aig_39_, lean_object* v_w_40_, lean_object* v_input_41_, lean_object* v_newWidth_42_, lean_object* v_curr_43_, lean_object* v_hcurr_44_, lean_object* v_s_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_39_, v_w_40_, v_input_41_, v_newWidth_42_, v_curr_43_, v_s_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_aig_50_, lean_object* v_w_51_, lean_object* v_input_52_, lean_object* v_newWidth_53_, lean_object* v_curr_54_, lean_object* v_hcurr_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(v_00_u03b1_47_, v_inst_48_, v_inst_49_, v_aig_50_, v_w_51_, v_input_52_, v_newWidth_53_, v_curr_54_, v_hcurr_55_, v_s_56_);
lean_dec(v_newWidth_53_);
lean_dec_ref(v_input_52_);
lean_dec(v_w_51_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object* v_newWidth_58_, lean_object* v_aig_59_, lean_object* v_target_60_){
_start:
{
lean_object* v_w_61_; lean_object* v_vec_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_w_61_ = lean_ctor_get(v_target_60_, 0);
v_vec_62_ = lean_ctor_get(v_target_60_, 1);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_mk_empty_array_with_capacity(v_newWidth_58_);
v___x_65_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_59_, v_w_61_, v_vec_62_, v_newWidth_58_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg___boxed(lean_object* v_newWidth_66_, lean_object* v_aig_67_, lean_object* v_target_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_newWidth_66_, v_aig_67_, v_target_68_);
lean_dec_ref(v_target_68_);
lean_dec(v_newWidth_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_newWidth_73_, lean_object* v_aig_74_, lean_object* v_target_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_newWidth_73_, v_aig_74_, v_target_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___boxed(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_newWidth_80_, lean_object* v_aig_81_, lean_object* v_target_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(v_00_u03b1_77_, v_inst_78_, v_inst_79_, v_newWidth_80_, v_aig_81_, v_target_82_);
lean_dec_ref(v_target_82_);
lean_dec(v_newWidth_80_);
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
return v_res_83_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin) {
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
}
#ifdef __cplusplus
}
#endif
