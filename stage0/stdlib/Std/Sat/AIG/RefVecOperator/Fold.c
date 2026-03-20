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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* v___y_8_; uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_lt(v_idx_3_, v_len_4_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v_f_6_);
lean_dec(v_idx_3_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_aig_1_);
lean_ctor_set(v___x_17_, 1, v_acc_2_);
return v___x_17_;
}
else
{
lean_object* v_ref_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_ref_18_ = lean_array_fget_borrowed(v_input_5_, v_idx_3_);
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = lean_nat_shiftr(v_ref_18_, v___x_19_);
v___x_21_ = lean_nat_land(v___x_19_, v_ref_18_);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_24_, 0, v___x_20_);
lean_ctor_set_uint8(v___x_24_, sizeof(void*)*1, v___x_16_);
v___y_8_ = v___x_24_;
goto v___jp_7_;
}
else
{
uint8_t v___x_25_; lean_object* v___x_26_; 
v___x_25_ = 0;
v___x_26_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_26_, 0, v___x_20_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*1, v___x_25_);
v___y_8_ = v___x_26_;
goto v___jp_7_;
}
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v_res_10_; lean_object* v_aig_11_; lean_object* v_ref_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_acc_2_);
lean_ctor_set(v___x_9_, 1, v___y_8_);
lean_inc_ref(v_f_6_);
v_res_10_ = lean_apply_2(v_f_6_, v_aig_1_, v___x_9_);
v_aig_11_ = lean_ctor_get(v_res_10_, 0);
lean_inc_ref(v_aig_11_);
v_ref_12_ = lean_ctor_get(v_res_10_, 1);
lean_inc_ref(v_ref_12_);
lean_dec_ref(v_res_10_);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_add(v_idx_3_, v___x_13_);
lean_dec(v_idx_3_);
v_aig_1_ = v_aig_11_;
v_acc_2_ = v_ref_12_;
v_idx_3_ = v___x_14_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___redArg___boxed(lean_object* v_aig_27_, lean_object* v_acc_28_, lean_object* v_idx_29_, lean_object* v_len_30_, lean_object* v_input_31_, lean_object* v_f_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_27_, v_acc_28_, v_idx_29_, v_len_30_, v_input_31_, v_f_32_);
lean_dec_ref(v_input_31_);
lean_dec(v_len_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go(lean_object* v_00_u03b1_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_aig_37_, lean_object* v_acc_38_, lean_object* v_idx_39_, lean_object* v_len_40_, lean_object* v_input_41_, lean_object* v_f_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_37_, v_acc_38_, v_idx_39_, v_len_40_, v_input_41_, v_f_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold_go___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_aig_48_, lean_object* v_acc_49_, lean_object* v_idx_50_, lean_object* v_len_51_, lean_object* v_input_52_, lean_object* v_f_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Sat_AIG_RefVec_fold_go(v_00_u03b1_45_, v_inst_46_, v_inst_47_, v_aig_48_, v_acc_49_, v_idx_50_, v_len_51_, v_input_52_, v_f_53_, v_inst_54_);
lean_dec_ref(v_input_52_);
lean_dec(v_len_51_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg(lean_object* v_len_59_, lean_object* v_aig_60_, lean_object* v_vec_61_, lean_object* v_func_62_){
_start:
{
lean_object* v___x_63_; lean_object* v_acc_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v_acc_64_ = ((lean_object*)(l_Std_Sat_AIG_RefVec_fold___redArg___closed__0));
v___x_65_ = l_Std_Sat_AIG_RefVec_fold_go___redArg(v_aig_60_, v_acc_64_, v___x_63_, v_len_59_, v_vec_61_, v_func_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___redArg___boxed(lean_object* v_len_66_, lean_object* v_aig_67_, lean_object* v_vec_68_, lean_object* v_func_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_len_66_, v_aig_67_, v_vec_68_, v_func_69_);
lean_dec_ref(v_vec_68_);
lean_dec(v_len_66_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_len_74_, lean_object* v_aig_75_, lean_object* v_vec_76_, lean_object* v_func_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_len_74_, v_aig_75_, v_vec_76_, v_func_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_fold___boxed(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_len_83_, lean_object* v_aig_84_, lean_object* v_vec_85_, lean_object* v_func_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Sat_AIG_RefVec_fold(v_00_u03b1_80_, v_inst_81_, v_inst_82_, v_len_83_, v_aig_84_, v_vec_85_, v_func_86_, v_inst_87_);
lean_dec_ref(v_vec_85_);
lean_dec(v_len_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
return v_res_88_;
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
