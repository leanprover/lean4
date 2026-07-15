// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Map
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___redArg(lean_object* v_len_1_, lean_object* v_aig_2_, lean_object* v_idx_3_, lean_object* v_s_4_, lean_object* v_input_5_, lean_object* v_f_6_){
_start:
{
lean_object* v___y_8_; uint8_t v___x_22_; 
v___x_22_ = lean_nat_dec_lt(v_idx_3_, v_len_1_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
lean_dec_ref(v_f_6_);
lean_dec(v_idx_3_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v_aig_2_);
lean_ctor_set(v___x_23_, 1, v_s_4_);
return v___x_23_;
}
else
{
lean_object* v_ref_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_ref_24_ = lean_array_fget_borrowed(v_input_5_, v_idx_3_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_shiftr(v_ref_24_, v___x_25_);
v___x_27_ = lean_nat_land(v___x_25_, v_ref_24_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v___x_22_);
v___y_8_ = v___x_30_;
goto v___jp_7_;
}
else
{
uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_32_, 0, v___x_26_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*1, v___x_31_);
v___y_8_ = v___x_32_;
goto v___jp_7_;
}
}
v___jp_7_:
{
lean_object* v_res_9_; lean_object* v_ref_10_; lean_object* v_aig_11_; lean_object* v_gate_12_; uint8_t v_invert_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_s_20_; 
lean_inc_ref(v_f_6_);
v_res_9_ = lean_apply_2(v_f_6_, v_aig_2_, v___y_8_);
v_ref_10_ = lean_ctor_get(v_res_9_, 1);
lean_inc_ref(v_ref_10_);
v_aig_11_ = lean_ctor_get(v_res_9_, 0);
lean_inc_ref(v_aig_11_);
lean_dec_ref(v_res_9_);
v_gate_12_ = lean_ctor_get(v_ref_10_, 0);
lean_inc(v_gate_12_);
v_invert_13_ = lean_ctor_get_uint8(v_ref_10_, sizeof(void*)*1);
lean_dec_ref(v_ref_10_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_idx_3_, v___x_14_);
lean_dec(v_idx_3_);
v___x_16_ = lean_unsigned_to_nat(2u);
v___x_17_ = lean_nat_mul(v_gate_12_, v___x_16_);
lean_dec(v_gate_12_);
v___x_18_ = l_Bool_toNat(v_invert_13_);
v___x_19_ = lean_nat_lor(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
v_s_20_ = lean_array_push(v_s_4_, v___x_19_);
v_aig_2_ = v_aig_11_;
v_idx_3_ = v___x_15_;
v_s_4_ = v_s_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___redArg___boxed(lean_object* v_len_33_, lean_object* v_aig_34_, lean_object* v_idx_35_, lean_object* v_s_36_, lean_object* v_input_37_, lean_object* v_f_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_33_, v_aig_34_, v_idx_35_, v_s_36_, v_input_37_, v_f_38_);
lean_dec_ref(v_input_37_);
lean_dec(v_len_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_len_43_, lean_object* v_aig_44_, lean_object* v_idx_45_, lean_object* v_hidx_46_, lean_object* v_s_47_, lean_object* v_input_48_, lean_object* v_f_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_43_, v_aig_44_, v_idx_45_, v_s_47_, v_input_48_, v_f_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___boxed(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_len_56_, lean_object* v_aig_57_, lean_object* v_idx_58_, lean_object* v_hidx_59_, lean_object* v_s_60_, lean_object* v_input_61_, lean_object* v_f_62_, lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Sat_AIG_RefVec_map_go(v_00_u03b1_53_, v_inst_54_, v_inst_55_, v_len_56_, v_aig_57_, v_idx_58_, v_hidx_59_, v_s_60_, v_input_61_, v_f_62_, v_inst_63_, v_inst_64_);
lean_dec_ref(v_input_61_);
lean_dec(v_len_56_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_54_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg(lean_object* v_len_66_, lean_object* v_aig_67_, lean_object* v_target_68_){
_start:
{
lean_object* v_vec_69_; lean_object* v_func_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_vec_69_ = lean_ctor_get(v_target_68_, 0);
lean_inc_ref(v_vec_69_);
v_func_70_ = lean_ctor_get(v_target_68_, 1);
lean_inc_ref(v_func_70_);
lean_dec_ref(v_target_68_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_mk_empty_array_with_capacity(v_len_66_);
v___x_73_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_66_, v_aig_67_, v___x_71_, v___x_72_, v_vec_69_, v_func_70_);
lean_dec_ref(v_vec_69_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg___boxed(lean_object* v_len_74_, lean_object* v_aig_75_, lean_object* v_target_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_74_, v_aig_75_, v_target_76_);
lean_dec(v_len_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_len_81_, lean_object* v_aig_82_, lean_object* v_target_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_81_, v_aig_82_, v_target_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___boxed(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_len_88_, lean_object* v_aig_89_, lean_object* v_target_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Sat_AIG_RefVec_map(v_00_u03b1_85_, v_inst_86_, v_inst_87_, v_len_88_, v_aig_89_, v_target_90_);
lean_dec(v_len_88_);
lean_dec_ref(v_inst_87_);
lean_dec_ref(v_inst_86_);
return v_res_91_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RefVecOperator_Map(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_RefVecOperator_Map(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RefVecOperator_Map(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
}
#ifdef __cplusplus
}
#endif
