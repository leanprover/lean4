// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(lean_object* v_w_1_, lean_object* v_val_2_, lean_object* v_curr_3_, lean_object* v_s_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_curr_3_, v_w_1_);
if (v___x_5_ == 0)
{
lean_dec(v_curr_3_);
return v_s_4_;
}
else
{
uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_s_12_; 
v___x_6_ = l_Nat_testBit(v_val_2_, v_curr_3_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_curr_3_, v___x_7_);
lean_dec(v_curr_3_);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_Bool_toNat(v___x_6_);
v___x_11_ = lean_nat_lor(v___x_9_, v___x_10_);
lean_dec(v___x_10_);
v_s_12_ = lean_array_push(v_s_4_, v___x_11_);
v_curr_3_ = v___x_8_;
v_s_4_ = v_s_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg___boxed(lean_object* v_w_14_, lean_object* v_val_15_, lean_object* v_curr_16_, lean_object* v_s_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(v_w_14_, v_val_15_, v_curr_16_, v_s_17_);
lean_dec(v_val_15_);
lean_dec(v_w_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_w_22_, lean_object* v_aig_23_, lean_object* v_val_24_, lean_object* v_curr_25_, lean_object* v_s_26_, lean_object* v_hcurr_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(v_w_22_, v_val_24_, v_curr_25_, v_s_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_w_32_, lean_object* v_aig_33_, lean_object* v_val_34_, lean_object* v_curr_35_, lean_object* v_s_36_, lean_object* v_hcurr_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go(v_00_u03b1_29_, v_inst_30_, v_inst_31_, v_w_32_, v_aig_33_, v_val_34_, v_curr_35_, v_s_36_, v_hcurr_37_);
lean_dec(v_val_34_);
lean_dec_ref(v_aig_33_);
lean_dec(v_w_32_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object* v_w_39_, lean_object* v_val_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_mk_empty_array_with_capacity(v_w_39_);
v___x_43_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(v_w_39_, v_val_40_, v___x_41_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg___boxed(lean_object* v_w_44_, lean_object* v_val_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_44_, v_val_45_);
lean_dec(v_val_45_);
lean_dec(v_w_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_w_50_, lean_object* v_aig_51_, lean_object* v_val_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_50_, v_val_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___boxed(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_w_57_, lean_object* v_aig_58_, lean_object* v_val_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst(v_00_u03b1_54_, v_inst_55_, v_inst_56_, v_w_57_, v_aig_58_, v_val_59_);
lean_dec(v_val_59_);
lean_dec_ref(v_aig_58_);
lean_dec(v_w_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_inst_55_);
return v_res_60_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin) {
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
}
#ifdef __cplusplus
}
#endif
