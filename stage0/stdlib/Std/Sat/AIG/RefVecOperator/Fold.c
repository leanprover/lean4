// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Fold
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_RefVec_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_RefVec_fold___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_RefVec_fold___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___redArg(lean_object* v_aig_1_, lean_object* v_acc_2_, lean_object* v_idx_3_, lean_object* v_len_4_, lean_object* v_input_5_, lean_object* v_f_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_idx_3_, v_len_4_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec_ref(v_f_6_);
lean_dec(v_idx_3_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_aig_1_);
lean_ctor_set(v___x_8_, 1, v_acc_2_);
return v___x_8_;
}
else
{
lean_object* v_ref_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_res_18_; lean_object* v_aig_19_; lean_object* v_ref_20_; lean_object* v___x_21_; 
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
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_acc_2_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
lean_inc_ref(v_f_6_);
v_res_18_ = lean_apply_2(v_f_6_, v_aig_1_, v___x_17_);
v_aig_19_ = lean_ctor_get(v_res_18_, 0);
lean_inc_ref(v_aig_19_);
v_ref_20_ = lean_ctor_get(v_res_18_, 1);
lean_inc_ref(v_ref_20_);
lean_dec_ref(v_res_18_);
v___x_21_ = lean_nat_add(v_idx_3_, v___x_10_);
lean_dec(v_idx_3_);
v_aig_1_ = v_aig_19_;
v_acc_2_ = v_ref_20_;
v_idx_3_ = v___x_21_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___redArg___boxed(lean_object* v_aig_23_, lean_object* v_acc_24_, lean_object* v_idx_25_, lean_object* v_len_26_, lean_object* v_input_27_, lean_object* v_f_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_23_, v_acc_24_, v_idx_25_, v_len_26_, v_input_27_, v_f_28_);
lean_dec_ref(v_input_27_);
lean_dec(v_len_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_aig_33_, lean_object* v_acc_34_, lean_object* v_idx_35_, lean_object* v_len_36_, lean_object* v_input_37_, lean_object* v_f_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_33_, v_acc_34_, v_idx_35_, v_len_36_, v_input_37_, v_f_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_aig_44_, lean_object* v_acc_45_, lean_object* v_idx_46_, lean_object* v_len_47_, lean_object* v_input_48_, lean_object* v_f_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Sat_AIG_RefVec_fold_go(v_00_u03b1_41_, v_inst_42_, v_inst_43_, v_aig_44_, v_acc_45_, v_idx_46_, v_len_47_, v_input_48_, v_f_49_, v_inst_50_);
lean_dec_ref(v_input_48_);
lean_dec(v_len_47_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg(lean_object* v_len_55_, lean_object* v_aig_56_, lean_object* v_vec_57_, lean_object* v_func_58_){
_start:
{
lean_object* v___x_59_; lean_object* v_acc_60_; lean_object* v___x_61_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v_acc_60_ = ((lean_object*)(l_Std_Sat_AIG_RefVec_fold___redArg___closed__0));
v___x_61_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_56_, v_acc_60_, v___x_59_, v_len_55_, v_vec_57_, v_func_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg___boxed(lean_object* v_len_62_, lean_object* v_aig_63_, lean_object* v_vec_64_, lean_object* v_func_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_len_62_, v_aig_63_, v_vec_64_, v_func_65_);
lean_dec_ref(v_vec_64_);
lean_dec(v_len_62_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_len_70_, lean_object* v_aig_71_, lean_object* v_vec_72_, lean_object* v_func_73_, lean_object* v_inst_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_len_70_, v_aig_71_, v_vec_72_, v_func_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___boxed(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_len_79_, lean_object* v_aig_80_, lean_object* v_vec_81_, lean_object* v_func_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Sat_AIG_RefVec_fold(v_00_u03b1_76_, v_inst_77_, v_inst_78_, v_len_79_, v_aig_80_, v_vec_81_, v_func_82_, v_inst_83_);
lean_dec_ref(v_vec_81_);
lean_dec(v_len_79_);
lean_dec_ref(v_inst_78_);
lean_dec_ref(v_inst_77_);
return v_res_84_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RefVecOperator_Fold(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_RefVecOperator_Fold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RefVecOperator_Fold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_RefVecOperator_Fold(builtin);
}
#ifdef __cplusplus
}
#endif
