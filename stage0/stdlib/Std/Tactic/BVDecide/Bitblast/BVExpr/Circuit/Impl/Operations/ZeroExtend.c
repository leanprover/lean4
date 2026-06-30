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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* v_gate_8_; uint8_t v_invert_9_; uint8_t v___x_18_; 
v___x_18_ = lean_nat_dec_lt(v_curr_5_, v_newWidth_4_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec(v_curr_5_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v_aig_1_);
lean_ctor_set(v___x_19_, 1, v_s_6_);
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_lt(v_curr_5_, v_w_2_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_s_24_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_curr_5_, v___x_21_);
lean_dec(v_curr_5_);
v___x_23_ = l_Bool_toNat(v___x_20_);
v_s_24_ = lean_array_push(v_s_6_, v___x_23_);
v_curr_5_ = v___x_22_;
v_s_6_ = v_s_24_;
goto _start;
}
else
{
lean_object* v_ref_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_ref_26_ = lean_array_fget_borrowed(v_input_3_, v_curr_5_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_shiftr(v_ref_26_, v___x_27_);
v___x_29_ = lean_nat_land(v___x_27_, v_ref_26_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
lean_dec(v___x_29_);
if (v___x_31_ == 0)
{
v_gate_8_ = v___x_28_;
v_invert_9_ = v___x_20_;
goto v___jp_7_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
v_gate_8_ = v___x_28_;
v_invert_9_ = v___x_32_;
goto v___jp_7_;
}
}
}
v___jp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_s_16_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_curr_5_, v___x_10_);
lean_dec(v_curr_5_);
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_nat_mul(v_gate_8_, v___x_12_);
lean_dec(v_gate_8_);
v___x_14_ = l_Bool_toNat(v_invert_9_);
v___x_15_ = lean_nat_lor(v___x_13_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_13_);
v_s_16_ = lean_array_push(v_s_6_, v___x_15_);
v_curr_5_ = v___x_11_;
v_s_6_ = v_s_16_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg___boxed(lean_object* v_aig_33_, lean_object* v_w_34_, lean_object* v_input_35_, lean_object* v_newWidth_36_, lean_object* v_curr_37_, lean_object* v_s_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_33_, v_w_34_, v_input_35_, v_newWidth_36_, v_curr_37_, v_s_38_);
lean_dec(v_newWidth_36_);
lean_dec_ref(v_input_35_);
lean_dec(v_w_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_aig_43_, lean_object* v_w_44_, lean_object* v_input_45_, lean_object* v_newWidth_46_, lean_object* v_curr_47_, lean_object* v_hcurr_48_, lean_object* v_s_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_43_, v_w_44_, v_input_45_, v_newWidth_46_, v_curr_47_, v_s_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___boxed(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_aig_54_, lean_object* v_w_55_, lean_object* v_input_56_, lean_object* v_newWidth_57_, lean_object* v_curr_58_, lean_object* v_hcurr_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(v_00_u03b1_51_, v_inst_52_, v_inst_53_, v_aig_54_, v_w_55_, v_input_56_, v_newWidth_57_, v_curr_58_, v_hcurr_59_, v_s_60_);
lean_dec(v_newWidth_57_);
lean_dec_ref(v_input_56_);
lean_dec(v_w_55_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object* v_newWidth_62_, lean_object* v_aig_63_, lean_object* v_target_64_){
_start:
{
lean_object* v_w_65_; lean_object* v_vec_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_w_65_ = lean_ctor_get(v_target_64_, 0);
v_vec_66_ = lean_ctor_get(v_target_64_, 1);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_mk_empty_array_with_capacity(v_newWidth_62_);
v___x_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(v_aig_63_, v_w_65_, v_vec_66_, v_newWidth_62_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg___boxed(lean_object* v_newWidth_70_, lean_object* v_aig_71_, lean_object* v_target_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_newWidth_70_, v_aig_71_, v_target_72_);
lean_dec_ref(v_target_72_);
lean_dec(v_newWidth_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_newWidth_77_, lean_object* v_aig_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_newWidth_77_, v_aig_78_, v_target_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_newWidth_84_, lean_object* v_aig_85_, lean_object* v_target_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_newWidth_84_, v_aig_85_, v_target_86_);
lean_dec_ref(v_target_86_);
lean_dec(v_newWidth_84_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
return v_res_87_;
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
