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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_idx_3_, v_len_1_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v_f_7_);
lean_dec(v_idx_3_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_aig_2_);
lean_ctor_set(v___x_9_, 1, v_s_4_);
return v___x_9_;
}
else
{
lean_object* v_ref_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v_ref_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_res_25_; lean_object* v_ref_26_; lean_object* v_aig_27_; lean_object* v_gate_28_; uint8_t v_invert_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_s_35_; 
v_ref_10_ = lean_array_fget_borrowed(v_lhs_5_, v_idx_3_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_land(v___x_11_, v_ref_10_);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_nat_shiftr(v_ref_10_, v___x_11_);
v___x_16_ = lean_bool_not(v___x_14_);
v___x_17_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*1, v___x_16_);
v_ref_18_ = lean_array_fget_borrowed(v_rhs_6_, v_idx_3_);
v___x_19_ = lean_nat_shiftr(v_ref_18_, v___x_11_);
v___x_20_ = lean_nat_land(v___x_11_, v_ref_18_);
v___x_21_ = lean_nat_dec_eq(v___x_20_, v___x_13_);
lean_dec(v___x_20_);
v___x_22_ = lean_bool_not(v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_23_, 0, v___x_19_);
lean_ctor_set_uint8(v___x_23_, sizeof(void*)*1, v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_17_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
lean_inc_ref(v_f_7_);
v_res_25_ = lean_apply_2(v_f_7_, v_aig_2_, v___x_24_);
v_ref_26_ = lean_ctor_get(v_res_25_, 1);
lean_inc_ref(v_ref_26_);
v_aig_27_ = lean_ctor_get(v_res_25_, 0);
lean_inc_ref(v_aig_27_);
lean_dec_ref(v_res_25_);
v_gate_28_ = lean_ctor_get(v_ref_26_, 0);
lean_inc(v_gate_28_);
v_invert_29_ = lean_ctor_get_uint8(v_ref_26_, sizeof(void*)*1);
lean_dec_ref(v_ref_26_);
v___x_30_ = lean_nat_add(v_idx_3_, v___x_11_);
lean_dec(v_idx_3_);
v___x_31_ = lean_unsigned_to_nat(2u);
v___x_32_ = lean_nat_mul(v_gate_28_, v___x_31_);
lean_dec(v_gate_28_);
v___x_33_ = lean_bool_to_nat(v_invert_29_);
v___x_34_ = lean_nat_lor(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
v_s_35_ = lean_array_push(v_s_4_, v___x_34_);
v_aig_2_ = v_aig_27_;
v_idx_3_ = v___x_30_;
v_s_4_ = v_s_35_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___redArg___boxed(lean_object* v_len_37_, lean_object* v_aig_38_, lean_object* v_idx_39_, lean_object* v_s_40_, lean_object* v_lhs_41_, lean_object* v_rhs_42_, lean_object* v_f_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_37_, v_aig_38_, v_idx_39_, v_s_40_, v_lhs_41_, v_rhs_42_, v_f_43_);
lean_dec_ref(v_rhs_42_);
lean_dec_ref(v_lhs_41_);
lean_dec(v_len_37_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_len_48_, lean_object* v_aig_49_, lean_object* v_idx_50_, lean_object* v_s_51_, lean_object* v_hidx_52_, lean_object* v_lhs_53_, lean_object* v_rhs_54_, lean_object* v_f_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_48_, v_aig_49_, v_idx_50_, v_s_51_, v_lhs_53_, v_rhs_54_, v_f_55_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___boxed(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_len_62_, lean_object* v_aig_63_, lean_object* v_idx_64_, lean_object* v_s_65_, lean_object* v_hidx_66_, lean_object* v_lhs_67_, lean_object* v_rhs_68_, lean_object* v_f_69_, lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Sat_AIG_RefVec_zip_go(v_00_u03b1_59_, v_inst_60_, v_inst_61_, v_len_62_, v_aig_63_, v_idx_64_, v_s_65_, v_hidx_66_, v_lhs_67_, v_rhs_68_, v_f_69_, v_inst_70_, v_inst_71_);
lean_dec_ref(v_rhs_68_);
lean_dec_ref(v_lhs_67_);
lean_dec(v_len_62_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg(lean_object* v_len_73_, lean_object* v_aig_74_, lean_object* v_input_75_, lean_object* v_func_76_){
_start:
{
lean_object* v_lhs_77_; lean_object* v_rhs_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_lhs_77_ = lean_ctor_get(v_input_75_, 0);
v_rhs_78_ = lean_ctor_get(v_input_75_, 1);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_mk_empty_array_with_capacity(v_len_73_);
v___x_81_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(v_len_73_, v_aig_74_, v___x_79_, v___x_80_, v_lhs_77_, v_rhs_78_, v_func_76_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___redArg___boxed(lean_object* v_len_82_, lean_object* v_aig_83_, lean_object* v_input_84_, lean_object* v_func_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_len_82_, v_aig_83_, v_input_84_, v_func_85_);
lean_dec_ref(v_input_84_);
lean_dec(v_len_82_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_len_90_, lean_object* v_aig_91_, lean_object* v_input_92_, lean_object* v_func_93_, lean_object* v_inst_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_len_90_, v_aig_91_, v_input_92_, v_func_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___boxed(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_len_100_, lean_object* v_aig_101_, lean_object* v_input_102_, lean_object* v_func_103_, lean_object* v_inst_104_, lean_object* v_inst_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Sat_AIG_RefVec_zip(v_00_u03b1_97_, v_inst_98_, v_inst_99_, v_len_100_, v_aig_101_, v_input_102_, v_func_103_, v_inst_104_, v_inst_105_);
lean_dec_ref(v_input_102_);
lean_dec(v_len_100_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
return v_res_106_;
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
