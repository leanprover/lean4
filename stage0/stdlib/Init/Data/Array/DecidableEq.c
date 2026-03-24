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
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_x_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, lean_box(0));
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_x_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_xs_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_27_, v_xs_28_, v_motive_29_, v_x_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_30_);
lean_dec_ref(v_xs_28_);
return v_res_34_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_apply_2(v_inst_35_, v_a_36_, v_b_37_);
v___x_39_ = lean_unbox(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object* v_inst_40_, lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_40_, v_a_41_, v_b_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object* v_inst_45_, lean_object* v_xs_46_, lean_object* v_ys_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_48_ = lean_array_get_size(v_xs_46_);
v___x_49_ = lean_array_get_size(v_ys_47_);
v___x_50_ = lean_nat_dec_eq(v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_inst_45_);
return v___x_50_;
}
else
{
lean_object* v___f_51_; uint8_t v___x_52_; 
v___f_51_ = lean_alloc_closure((void*)(l_Array_instDecidableEqImpl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_51_, 0, v_inst_45_);
v___x_52_ = l_Array_isEqvAux___redArg(v_xs_46_, v_ys_47_, v___f_51_, v___x_48_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object* v_inst_53_, lean_object* v_xs_54_, lean_object* v_ys_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Array_instDecidableEqImpl___redArg(v_inst_53_, v_xs_54_, v_ys_55_);
lean_dec_ref(v_ys_55_);
lean_dec_ref(v_xs_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_xs_60_, lean_object* v_ys_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = l_Array_instDecidableEqImpl___redArg(v_inst_59_, v_xs_60_, v_ys_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_xs_65_, lean_object* v_ys_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Array_instDecidableEqImpl(v_00_u03b1_63_, v_inst_64_, v_xs_65_, v_ys_66_);
lean_dec_ref(v_ys_66_);
lean_dec_ref(v_xs_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object* v_inst_69_, lean_object* v_xs_70_, lean_object* v_ys_71_){
_start:
{
lean_object* v_toList_72_; 
lean_inc_ref(v_xs_70_);
v_toList_72_ = lean_array_to_list(v_xs_70_);
if (lean_obj_tag(v_toList_72_) == 0)
{
lean_object* v_toList_73_; 
lean_dec_ref(v_xs_70_);
lean_dec_ref(v_inst_69_);
v_toList_73_ = lean_array_to_list(v_ys_71_);
if (lean_obj_tag(v_toList_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
lean_dec_ref(v_toList_73_);
v___x_75_ = 0;
return v___x_75_;
}
}
else
{
lean_object* v_toList_76_; 
lean_dec_ref(v_toList_72_);
lean_inc_ref(v_ys_71_);
v_toList_76_ = lean_array_to_list(v_ys_71_);
if (lean_obj_tag(v_toList_76_) == 0)
{
uint8_t v___x_77_; 
lean_dec_ref(v_ys_71_);
lean_dec_ref(v_xs_70_);
lean_dec_ref(v_inst_69_);
v___x_77_ = 0;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
lean_dec_ref(v_toList_76_);
v___x_78_ = l_Array_instDecidableEqImpl___redArg(v_inst_69_, v_xs_70_, v_ys_71_);
lean_dec_ref(v_ys_71_);
lean_dec_ref(v_xs_70_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object* v_inst_79_, lean_object* v_xs_80_, lean_object* v_ys_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Array_instDecidableEq___redArg(v_inst_79_, v_xs_80_, v_ys_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_xs_86_, lean_object* v_ys_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = l_Array_instDecidableEq___redArg(v_inst_85_, v_xs_86_, v_ys_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_xs_91_, lean_object* v_ys_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Array_instDecidableEq(v_00_u03b1_89_, v_inst_90_, v_xs_91_, v_ys_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object* v_xs_95_){
_start:
{
lean_object* v_toList_96_; 
v_toList_96_ = lean_array_to_list(v_xs_95_);
if (lean_obj_tag(v_toList_96_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
lean_dec_ref(v_toList_96_);
v___x_98_ = 0;
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object* v_xs_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Array_instDecidableEqEmp___redArg(v_xs_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object* v_00_u03b1_102_, lean_object* v_xs_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_Array_instDecidableEqEmp___redArg(v_xs_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object* v_00_u03b1_105_, lean_object* v_xs_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Array_instDecidableEqEmp(v_00_u03b1_105_, v_xs_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object* v_ys_109_){
_start:
{
lean_object* v_toList_110_; 
v_toList_110_ = lean_array_to_list(v_ys_109_);
if (lean_obj_tag(v_toList_110_) == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
lean_dec_ref(v_toList_110_);
v___x_112_ = 0;
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object* v_ys_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Array_instDecidableEmpEq___redArg(v_ys_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object* v_00_u03b1_116_, lean_object* v_ys_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_Array_instDecidableEmpEq___redArg(v_ys_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object* v_00_u03b1_119_, lean_object* v_ys_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Array_instDecidableEmpEq(v_00_u03b1_119_, v_ys_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object* v_xs_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_array_get_size(v_xs_123_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object* v_xs_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_127_);
lean_dec_ref(v_xs_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object* v_00_u03b1_130_, lean_object* v_xs_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_array_get_size(v_xs_131_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_nat_dec_eq(v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object* v_00_u03b1_135_, lean_object* v_xs_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_135_, v_xs_136_);
lean_dec_ref(v_xs_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object* v_xs_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = lean_array_get_size(v_xs_139_);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object* v_xs_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_143_);
lean_dec_ref(v_xs_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object* v_00_u03b1_146_, lean_object* v_xs_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_array_get_size(v_xs_147_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object* v_00_u03b1_151_, lean_object* v_xs_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_151_, v_xs_152_);
lean_dec_ref(v_xs_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
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
