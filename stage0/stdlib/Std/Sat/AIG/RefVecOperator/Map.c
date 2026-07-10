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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_idx_3_, v_len_1_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec_ref(v_f_6_);
lean_dec(v_idx_3_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_aig_2_);
lean_ctor_set(v___x_8_, 1, v_s_4_);
return v___x_8_;
}
else
{
lean_object* v_ref_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v_res_17_; lean_object* v_ref_18_; lean_object* v_aig_19_; lean_object* v_gate_20_; uint8_t v_invert_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_s_27_; 
v_ref_9_ = lean_array_fget_borrowed(v_input_5_, v_idx_3_);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_shiftr(v_ref_9_, v___x_10_);
v___x_12_ = lean_nat_land(v___x_10_, v_ref_9_);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_bool_not(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_16_, 0, v___x_11_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_15_);
lean_inc_ref(v_f_6_);
v_res_17_ = lean_apply_2(v_f_6_, v_aig_2_, v___x_16_);
v_ref_18_ = lean_ctor_get(v_res_17_, 1);
lean_inc_ref(v_ref_18_);
v_aig_19_ = lean_ctor_get(v_res_17_, 0);
lean_inc_ref(v_aig_19_);
lean_dec_ref(v_res_17_);
v_gate_20_ = lean_ctor_get(v_ref_18_, 0);
lean_inc(v_gate_20_);
v_invert_21_ = lean_ctor_get_uint8(v_ref_18_, sizeof(void*)*1);
lean_dec_ref(v_ref_18_);
v___x_22_ = lean_nat_add(v_idx_3_, v___x_10_);
lean_dec(v_idx_3_);
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_nat_mul(v_gate_20_, v___x_23_);
lean_dec(v_gate_20_);
v___x_25_ = lean_bool_to_nat(v_invert_21_);
v___x_26_ = lean_nat_lor(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
v_s_27_ = lean_array_push(v_s_4_, v___x_26_);
v_aig_2_ = v_aig_19_;
v_idx_3_ = v___x_22_;
v_s_4_ = v_s_27_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___redArg___boxed(lean_object* v_len_29_, lean_object* v_aig_30_, lean_object* v_idx_31_, lean_object* v_s_32_, lean_object* v_input_33_, lean_object* v_f_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_29_, v_aig_30_, v_idx_31_, v_s_32_, v_input_33_, v_f_34_);
lean_dec_ref(v_input_33_);
lean_dec(v_len_29_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_len_39_, lean_object* v_aig_40_, lean_object* v_idx_41_, lean_object* v_hidx_42_, lean_object* v_s_43_, lean_object* v_input_44_, lean_object* v_f_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_39_, v_aig_40_, v_idx_41_, v_s_43_, v_input_44_, v_f_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map_go___boxed(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_len_52_, lean_object* v_aig_53_, lean_object* v_idx_54_, lean_object* v_hidx_55_, lean_object* v_s_56_, lean_object* v_input_57_, lean_object* v_f_58_, lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_Sat_AIG_RefVec_map_go(v_00_u03b1_49_, v_inst_50_, v_inst_51_, v_len_52_, v_aig_53_, v_idx_54_, v_hidx_55_, v_s_56_, v_input_57_, v_f_58_, v_inst_59_, v_inst_60_);
lean_dec_ref(v_input_57_);
lean_dec(v_len_52_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg(lean_object* v_len_62_, lean_object* v_aig_63_, lean_object* v_target_64_){
_start:
{
lean_object* v_vec_65_; lean_object* v_func_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_vec_65_ = lean_ctor_get(v_target_64_, 0);
lean_inc_ref(v_vec_65_);
v_func_66_ = lean_ctor_get(v_target_64_, 1);
lean_inc_ref(v_func_66_);
lean_dec_ref(v_target_64_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_mk_empty_array_with_capacity(v_len_62_);
v___x_69_ = l_Std_Sat_AIG_RefVec_map_go___redArg(v_len_62_, v_aig_63_, v___x_67_, v___x_68_, v_vec_65_, v_func_66_);
lean_dec_ref(v_vec_65_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___redArg___boxed(lean_object* v_len_70_, lean_object* v_aig_71_, lean_object* v_target_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_70_, v_aig_71_, v_target_72_);
lean_dec(v_len_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_len_77_, lean_object* v_aig_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_77_, v_aig_78_, v_target_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_map___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_len_84_, lean_object* v_aig_85_, lean_object* v_target_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Sat_AIG_RefVec_map(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_len_84_, v_aig_85_, v_target_86_);
lean_dec(v_len_84_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
return v_res_87_;
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
