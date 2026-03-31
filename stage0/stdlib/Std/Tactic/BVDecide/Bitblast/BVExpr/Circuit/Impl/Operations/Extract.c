// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(lean_object* v_newWidth_1_, lean_object* v_w_2_, lean_object* v_input_3_, lean_object* v_start_4_, lean_object* v_curr_5_, lean_object* v_s_6_){
_start:
{
lean_object* v_gate_8_; uint8_t v_invert_9_; uint8_t v___x_18_; 
v___x_18_ = lean_nat_dec_lt(v_curr_5_, v_newWidth_1_);
if (v___x_18_ == 0)
{
lean_dec(v_curr_5_);
return v_s_6_;
}
else
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_nat_add(v_start_4_, v_curr_5_);
v___x_20_ = lean_nat_dec_lt(v___x_19_, v_w_2_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v___x_19_);
v___x_21_ = lean_unsigned_to_nat(0u);
v_gate_8_ = v___x_21_;
v_invert_9_ = v___x_20_;
goto v___jp_7_;
}
else
{
lean_object* v_ref_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_ref_22_ = lean_array_fget_borrowed(v_input_3_, v___x_19_);
lean_dec(v___x_19_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_shiftr(v_ref_22_, v___x_23_);
v___x_25_ = lean_nat_land(v___x_23_, v_ref_22_);
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_nat_dec_eq(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
if (v___x_27_ == 0)
{
v_gate_8_ = v___x_24_;
v_invert_9_ = v___x_20_;
goto v___jp_7_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = 0;
v_gate_8_ = v___x_24_;
v_invert_9_ = v___x_28_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg___boxed(lean_object* v_newWidth_29_, lean_object* v_w_30_, lean_object* v_input_31_, lean_object* v_start_32_, lean_object* v_curr_33_, lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(v_newWidth_29_, v_w_30_, v_input_31_, v_start_32_, v_curr_33_, v_s_34_);
lean_dec(v_start_32_);
lean_dec_ref(v_input_31_);
lean_dec(v_w_30_);
lean_dec(v_newWidth_29_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_newWidth_39_, lean_object* v_aig_40_, lean_object* v_w_41_, lean_object* v_input_42_, lean_object* v_start_43_, lean_object* v_curr_44_, lean_object* v_hcurr_45_, lean_object* v_s_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(v_newWidth_39_, v_w_41_, v_input_42_, v_start_43_, v_curr_44_, v_s_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___boxed(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_newWidth_51_, lean_object* v_aig_52_, lean_object* v_w_53_, lean_object* v_input_54_, lean_object* v_start_55_, lean_object* v_curr_56_, lean_object* v_hcurr_57_, lean_object* v_s_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(v_00_u03b1_48_, v_inst_49_, v_inst_50_, v_newWidth_51_, v_aig_52_, v_w_53_, v_input_54_, v_start_55_, v_curr_56_, v_hcurr_57_, v_s_58_);
lean_dec(v_start_55_);
lean_dec_ref(v_input_54_);
lean_dec(v_w_53_);
lean_dec_ref(v_aig_52_);
lean_dec(v_newWidth_51_);
lean_dec_ref(v_inst_50_);
lean_dec_ref(v_inst_49_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(lean_object* v_newWidth_60_, lean_object* v_aig_61_, lean_object* v_target_62_){
_start:
{
lean_object* v_w_63_; lean_object* v_vec_64_; lean_object* v_start_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_w_63_ = lean_ctor_get(v_target_62_, 0);
v_vec_64_ = lean_ctor_get(v_target_62_, 1);
v_start_65_ = lean_ctor_get(v_target_62_, 2);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_mk_empty_array_with_capacity(v_newWidth_60_);
v___x_68_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(v_newWidth_60_, v_w_63_, v_vec_64_, v_start_65_, v___x_66_, v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_aig_61_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg___boxed(lean_object* v_newWidth_70_, lean_object* v_aig_71_, lean_object* v_target_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_newWidth_70_, v_aig_71_, v_target_72_);
lean_dec_ref(v_target_72_);
lean_dec(v_newWidth_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_newWidth_77_, lean_object* v_aig_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(v_newWidth_77_, v_aig_78_, v_target_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_newWidth_84_, lean_object* v_aig_85_, lean_object* v_target_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_newWidth_84_, v_aig_85_, v_target_86_);
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
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin) {
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
}
#ifdef __cplusplus
}
#endif
