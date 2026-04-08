// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(lean_object* v_n_1_, lean_object* v_input_2_, lean_object* v_curr_3_, lean_object* v_s_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_curr_3_, v_n_1_);
if (v___x_5_ == 0)
{
lean_dec(v_curr_3_);
return v_s_4_;
}
else
{
lean_object* v_s_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_s_6_ = l_Array_append___redArg(v_s_4_, v_input_2_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_curr_3_, v___x_7_);
lean_dec(v_curr_3_);
v_curr_3_ = v___x_8_;
v_s_4_ = v_s_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg___boxed(lean_object* v_n_10_, lean_object* v_input_11_, lean_object* v_curr_12_, lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(v_n_10_, v_input_11_, v_curr_12_, v_s_13_);
lean_dec_ref(v_input_11_);
lean_dec(v_n_10_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_aig_18_, lean_object* v_w_19_, lean_object* v_n_20_, lean_object* v_input_21_, lean_object* v_curr_22_, lean_object* v_hcurr_23_, lean_object* v_s_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(v_n_20_, v_input_21_, v_curr_22_, v_s_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_aig_29_, lean_object* v_w_30_, lean_object* v_n_31_, lean_object* v_input_32_, lean_object* v_curr_33_, lean_object* v_hcurr_34_, lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(v_00_u03b1_26_, v_inst_27_, v_inst_28_, v_aig_29_, v_w_30_, v_n_31_, v_input_32_, v_curr_33_, v_hcurr_34_, v_s_35_);
lean_dec_ref(v_input_32_);
lean_dec(v_n_31_);
lean_dec(v_w_30_);
lean_dec_ref(v_aig_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(lean_object* v_newWidth_37_, lean_object* v_aig_38_, lean_object* v_target_39_){
_start:
{
lean_object* v_n_40_; lean_object* v_inner_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_ref_44_; lean_object* v___x_45_; 
v_n_40_ = lean_ctor_get(v_target_39_, 1);
v_inner_41_ = lean_ctor_get(v_target_39_, 2);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_mk_empty_array_with_capacity(v_newWidth_37_);
v_ref_44_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(v_n_40_, v_inner_41_, v___x_42_, v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_aig_38_);
lean_ctor_set(v___x_45_, 1, v_ref_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg___boxed(lean_object* v_newWidth_46_, lean_object* v_aig_47_, lean_object* v_target_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(v_newWidth_46_, v_aig_47_, v_target_48_);
lean_dec_ref(v_target_48_);
lean_dec(v_newWidth_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_newWidth_53_, lean_object* v_aig_54_, lean_object* v_target_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(v_newWidth_53_, v_aig_54_, v_target_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___boxed(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_newWidth_60_, lean_object* v_aig_61_, lean_object* v_target_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(v_00_u03b1_57_, v_inst_58_, v_inst_59_, v_newWidth_60_, v_aig_61_, v_target_62_);
lean_dec_ref(v_target_62_);
lean_dec(v_newWidth_60_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___redArg(lean_object* v_target_64_, lean_object* v_h__1_65_){
_start:
{
lean_object* v_w_66_; lean_object* v_n_67_; lean_object* v_inner_68_; lean_object* v___x_69_; 
v_w_66_ = lean_ctor_get(v_target_64_, 0);
lean_inc(v_w_66_);
v_n_67_ = lean_ctor_get(v_target_64_, 1);
lean_inc(v_n_67_);
v_inner_68_ = lean_ctor_get(v_target_64_, 2);
lean_inc_ref(v_inner_68_);
lean_dec_ref(v_target_64_);
v___x_69_ = lean_apply_4(v_h__1_65_, v_w_66_, v_n_67_, v_inner_68_, lean_box(0));
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_newWidth_73_, lean_object* v_aig_74_, lean_object* v_motive_75_, lean_object* v_target_76_, lean_object* v_h__1_77_){
_start:
{
lean_object* v_w_78_; lean_object* v_n_79_; lean_object* v_inner_80_; lean_object* v___x_81_; 
v_w_78_ = lean_ctor_get(v_target_76_, 0);
lean_inc(v_w_78_);
v_n_79_ = lean_ctor_get(v_target_76_, 1);
lean_inc(v_n_79_);
v_inner_80_ = lean_ctor_get(v_target_76_, 2);
lean_inc_ref(v_inner_80_);
lean_dec_ref(v_target_76_);
v___x_81_ = lean_apply_4(v_h__1_77_, v_w_78_, v_n_79_, v_inner_80_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___boxed(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_newWidth_85_, lean_object* v_aig_86_, lean_object* v_motive_87_, lean_object* v_target_88_, lean_object* v_h__1_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(v_00_u03b1_82_, v_inst_83_, v_inst_84_, v_newWidth_85_, v_aig_86_, v_motive_87_, v_target_88_, v_h__1_89_);
lean_dec_ref(v_aig_86_);
lean_dec(v_newWidth_85_);
lean_dec_ref(v_inst_84_);
lean_dec_ref(v_inst_83_);
return v_res_90_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin) {
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin);
}
#ifdef __cplusplus
}
#endif
