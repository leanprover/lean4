// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Zip
// Imports: public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___redArg(lean_object* v_len_1_, lean_object* v_aig_2_, lean_object* v_idx_3_, lean_object* v_s_4_, lean_object* v_lhs_5_, lean_object* v_rhs_6_, lean_object* v_f_7_){
_start:
{
lean_object* v___y_9_; lean_object* v___y_10_; uint8_t v___x_25_; lean_object* v___y_27_; 
v___x_25_ = lean_nat_dec_lt(v_idx_3_, v_len_1_);
if (v___x_25_ == 0)
{
lean_object* v___x_37_; 
lean_dec_ref(v_f_7_);
lean_dec(v_idx_3_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v_aig_2_);
lean_ctor_set(v___x_37_, 1, v_s_4_);
return v___x_37_;
}
else
{
lean_object* v_ref_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_ref_38_ = lean_array_fget_borrowed(v_lhs_5_, v_idx_3_);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_shiftr(v_ref_38_, v___x_39_);
v___x_41_ = lean_nat_land(v___x_39_, v_ref_38_);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_nat_dec_eq(v___x_41_, v___x_42_);
lean_dec(v___x_41_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_25_);
v___y_27_ = v___x_44_;
goto v___jp_26_;
}
else
{
uint8_t v___x_45_; lean_object* v___x_46_; 
v___x_45_ = 0;
v___x_46_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_46_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_45_);
v___y_27_ = v___x_46_;
goto v___jp_26_;
}
}
v___jp_8_:
{
lean_object* v___x_11_; lean_object* v_res_12_; lean_object* v_ref_13_; lean_object* v_aig_14_; lean_object* v_gate_15_; uint8_t v_invert_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_s_23_; 
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___y_9_);
lean_ctor_set(v___x_11_, 1, v___y_10_);
lean_inc_ref(v_f_7_);
v_res_12_ = lean_apply_2(v_f_7_, v_aig_2_, v___x_11_);
v_ref_13_ = lean_ctor_get(v_res_12_, 1);
lean_inc_ref(v_ref_13_);
v_aig_14_ = lean_ctor_get(v_res_12_, 0);
lean_inc_ref(v_aig_14_);
lean_dec_ref(v_res_12_);
v_gate_15_ = lean_ctor_get(v_ref_13_, 0);
lean_inc(v_gate_15_);
v_invert_16_ = lean_ctor_get_uint8(v_ref_13_, sizeof(void*)*1);
lean_dec_ref(v_ref_13_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_idx_3_, v___x_17_);
lean_dec(v_idx_3_);
v___x_19_ = lean_unsigned_to_nat(2u);
v___x_20_ = lean_nat_mul(v_gate_15_, v___x_19_);
lean_dec(v_gate_15_);
v___x_21_ = l_Bool_toNat(v_invert_16_);
v___x_22_ = lean_nat_lor(v___x_20_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v___x_20_);
v_s_23_ = lean_array_push(v_s_4_, v___x_22_);
v_aig_2_ = v_aig_14_;
v_idx_3_ = v___x_18_;
v_s_4_ = v_s_23_;
goto _start;
}
v___jp_26_:
{
lean_object* v_ref_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_ref_28_ = lean_array_fget_borrowed(v_rhs_6_, v_idx_3_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_shiftr(v_ref_28_, v___x_29_);
v___x_31_ = lean_nat_land(v___x_29_, v_ref_28_);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_nat_dec_eq(v___x_31_, v___x_32_);
lean_dec(v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_34_, 0, v___x_30_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_25_);
v___y_9_ = v___y_27_;
v___y_10_ = v___x_34_;
goto v___jp_8_;
}
else
{
uint8_t v___x_35_; lean_object* v___x_36_; 
v___x_35_ = 0;
v___x_36_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_36_, 0, v___x_30_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*1, v___x_35_);
v___y_9_ = v___y_27_;
v___y_10_ = v___x_36_;
goto v___jp_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___redArg___boxed(lean_object* v_len_47_, lean_object* v_aig_48_, lean_object* v_idx_49_, lean_object* v_s_50_, lean_object* v_lhs_51_, lean_object* v_rhs_52_, lean_object* v_f_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_47_, v_aig_48_, v_idx_49_, v_s_50_, v_lhs_51_, v_rhs_52_, v_f_53_);
lean_dec_ref(v_rhs_52_);
lean_dec_ref(v_lhs_51_);
lean_dec(v_len_47_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_len_58_, lean_object* v_aig_59_, lean_object* v_idx_60_, lean_object* v_s_61_, lean_object* v_hidx_62_, lean_object* v_lhs_63_, lean_object* v_rhs_64_, lean_object* v_f_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_58_, v_aig_59_, v_idx_60_, v_s_61_, v_lhs_63_, v_rhs_64_, v_f_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___boxed(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_len_72_, lean_object* v_aig_73_, lean_object* v_idx_74_, lean_object* v_s_75_, lean_object* v_hidx_76_, lean_object* v_lhs_77_, lean_object* v_rhs_78_, lean_object* v_f_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_Sat_AIG_RefVec_zip_go(v_00_u03b1_69_, v_inst_70_, v_inst_71_, v_len_72_, v_aig_73_, v_idx_74_, v_s_75_, v_hidx_76_, v_lhs_77_, v_rhs_78_, v_f_79_, v_inst_80_, v_inst_81_);
lean_dec_ref(v_rhs_78_);
lean_dec_ref(v_lhs_77_);
lean_dec(v_len_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg(lean_object* v_len_83_, lean_object* v_aig_84_, lean_object* v_input_85_, lean_object* v_func_86_){
_start:
{
lean_object* v_lhs_87_; lean_object* v_rhs_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_lhs_87_ = lean_ctor_get(v_input_85_, 0);
v_rhs_88_ = lean_ctor_get(v_input_85_, 1);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_mk_empty_array_with_capacity(v_len_83_);
v___x_91_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_83_, v_aig_84_, v___x_89_, v___x_90_, v_lhs_87_, v_rhs_88_, v_func_86_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg___boxed(lean_object* v_len_92_, lean_object* v_aig_93_, lean_object* v_input_94_, lean_object* v_func_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_len_92_, v_aig_93_, v_input_94_, v_func_95_);
lean_dec_ref(v_input_94_);
lean_dec(v_len_92_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_len_100_, lean_object* v_aig_101_, lean_object* v_input_102_, lean_object* v_func_103_, lean_object* v_inst_104_, lean_object* v_inst_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_len_100_, v_aig_101_, v_input_102_, v_func_103_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___boxed(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_len_110_, lean_object* v_aig_111_, lean_object* v_input_112_, lean_object* v_func_113_, lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Sat_AIG_RefVec_zip(v_00_u03b1_107_, v_inst_108_, v_inst_109_, v_len_110_, v_aig_111_, v_input_112_, v_func_113_, v_inst_114_, v_inst_115_);
lean_dec_ref(v_input_112_);
lean_dec(v_len_110_);
lean_dec_ref(v_inst_109_);
lean_dec_ref(v_inst_108_);
return v_res_116_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RefVecOperator_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_RefVecOperator_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RefVecOperator_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
