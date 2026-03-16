// Lean compiler output
// Module: Init.Data.Array.DecidableEq
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Basic public import Init.Data.Nat.Lemmas import Init.ByCases import Init.Classical import Init.Data.BEq import Init.Data.Bool import Init.Data.List.Nat.BEq import Init.RCases
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_14_, lean_object* v_xs_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(v_x_17_, v_h__1_19_, v_h__2_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_xs_23_, lean_object* v_motive_24_, lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_22_, v_xs_23_, v_motive_24_, v_x_25_, v_x_26_, v_h__1_27_, v_h__2_28_);
lean_dec(v_x_25_);
lean_dec_ref(v_xs_23_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object* v_inst_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_apply_2(v_inst_30_, v_a_31_, v_b_32_);
v___x_34_ = lean_unbox(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_35_, v_a_36_, v_b_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object* v_inst_40_, lean_object* v_xs_41_, lean_object* v_ys_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = lean_array_get_size(v_xs_41_);
v___x_44_ = lean_array_get_size(v_ys_42_);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec_ref(v_inst_40_);
return v___x_45_;
}
else
{
lean_object* v___f_46_; uint8_t v___x_47_; 
v___f_46_ = lean_alloc_closure((void*)(l_Array_instDecidableEqImpl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_46_, 0, v_inst_40_);
v___x_47_ = l_Array_isEqvAux___redArg(v_xs_41_, v_ys_42_, v___f_46_, v___x_43_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object* v_inst_48_, lean_object* v_xs_49_, lean_object* v_ys_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Array_instDecidableEqImpl___redArg(v_inst_48_, v_xs_49_, v_ys_50_);
lean_dec_ref(v_ys_50_);
lean_dec_ref(v_xs_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_xs_55_, lean_object* v_ys_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = l_Array_instDecidableEqImpl___redArg(v_inst_54_, v_xs_55_, v_ys_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_xs_60_, lean_object* v_ys_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Array_instDecidableEqImpl(v_00_u03b1_58_, v_inst_59_, v_xs_60_, v_ys_61_);
lean_dec_ref(v_ys_61_);
lean_dec_ref(v_xs_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object* v_inst_64_, lean_object* v_xs_65_, lean_object* v_ys_66_){
_start:
{
lean_object* v_toList_67_; 
lean_inc_ref(v_xs_65_);
v_toList_67_ = lean_array_to_list(v_xs_65_);
if (lean_obj_tag(v_toList_67_) == 0)
{
lean_object* v_toList_68_; 
lean_dec_ref(v_xs_65_);
lean_dec_ref(v_inst_64_);
v_toList_68_ = lean_array_to_list(v_ys_66_);
if (lean_obj_tag(v_toList_68_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
lean_dec_ref(v_toList_68_);
v___x_70_ = 0;
return v___x_70_;
}
}
else
{
lean_object* v_toList_71_; 
lean_dec_ref(v_toList_67_);
lean_inc_ref(v_ys_66_);
v_toList_71_ = lean_array_to_list(v_ys_66_);
if (lean_obj_tag(v_toList_71_) == 0)
{
uint8_t v___x_72_; 
lean_dec_ref(v_ys_66_);
lean_dec_ref(v_xs_65_);
lean_dec_ref(v_inst_64_);
v___x_72_ = 0;
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec_ref(v_toList_71_);
v___x_73_ = l_Array_instDecidableEqImpl___redArg(v_inst_64_, v_xs_65_, v_ys_66_);
lean_dec_ref(v_ys_66_);
lean_dec_ref(v_xs_65_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object* v_inst_74_, lean_object* v_xs_75_, lean_object* v_ys_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Array_instDecidableEq___redArg(v_inst_74_, v_xs_75_, v_ys_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_xs_81_, lean_object* v_ys_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Array_instDecidableEq___redArg(v_inst_80_, v_xs_81_, v_ys_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_xs_86_, lean_object* v_ys_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Array_instDecidableEq(v_00_u03b1_84_, v_inst_85_, v_xs_86_, v_ys_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object* v_xs_90_){
_start:
{
lean_object* v_toList_91_; 
v_toList_91_ = lean_array_to_list(v_xs_90_);
if (lean_obj_tag(v_toList_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
lean_dec_ref(v_toList_91_);
v___x_93_ = 0;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object* v_xs_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Array_instDecidableEqEmp___redArg(v_xs_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object* v_00_u03b1_97_, lean_object* v_xs_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Array_instDecidableEqEmp___redArg(v_xs_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object* v_00_u03b1_100_, lean_object* v_xs_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Array_instDecidableEqEmp(v_00_u03b1_100_, v_xs_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object* v_ys_104_){
_start:
{
lean_object* v_toList_105_; 
v_toList_105_ = lean_array_to_list(v_ys_104_);
if (lean_obj_tag(v_toList_105_) == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
lean_dec_ref(v_toList_105_);
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object* v_ys_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Array_instDecidableEmpEq___redArg(v_ys_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object* v_00_u03b1_111_, lean_object* v_ys_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Array_instDecidableEmpEq___redArg(v_ys_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object* v_00_u03b1_114_, lean_object* v_ys_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Array_instDecidableEmpEq(v_00_u03b1_114_, v_ys_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object* v_xs_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_array_get_size(v_xs_118_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_nat_dec_eq(v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object* v_xs_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_122_);
lean_dec_ref(v_xs_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object* v_00_u03b1_125_, lean_object* v_xs_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_array_get_size(v_xs_126_);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_dec_eq(v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object* v_00_u03b1_130_, lean_object* v_xs_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_130_, v_xs_131_);
lean_dec_ref(v_xs_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object* v_xs_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_array_get_size(v_xs_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object* v_xs_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_138_);
lean_dec_ref(v_xs_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object* v_00_u03b1_141_, lean_object* v_xs_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = lean_array_get_size(v_xs_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object* v_00_u03b1_146_, lean_object* v_xs_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_146_, v_xs_147_);
lean_dec_ref(v_xs_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_DecidableEq(builtin);
}
#ifdef __cplusplus
}
#endif
