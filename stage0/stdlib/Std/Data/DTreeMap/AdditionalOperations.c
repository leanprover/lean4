// Lean compiler output
// Module: Std.Data.DTreeMap.AdditionalOperations
// Imports: public import Std.Data.DTreeMap.Raw.Basic public import Std.Data.DTreeMap.Internal.WF.Lemmas
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
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___redArg(lean_object* v_f_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_3_, v_t_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_00_u03b3_8_, lean_object* v_cmp_9_, lean_object* v_f_10_, lean_object* v_t_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_10_, v_t_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_00_u03b3_15_, lean_object* v_cmp_16_, lean_object* v_f_17_, lean_object* v_t_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_DTreeMap_filterMap(v_00_u03b1_13_, v_00_u03b2_14_, v_00_u03b3_15_, v_cmp_16_, v_f_17_, v_t_18_);
lean_dec_ref(v_cmp_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___redArg(lean_object* v_f_20_, lean_object* v_t_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_20_, v_t_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_00_u03b3_25_, lean_object* v_cmp_26_, lean_object* v_f_27_, lean_object* v_t_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_27_, v_t_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_00_u03b3_32_, lean_object* v_cmp_33_, lean_object* v_f_34_, lean_object* v_t_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_DTreeMap_map(v_00_u03b1_30_, v_00_u03b2_31_, v_00_u03b3_32_, v_cmp_33_, v_f_34_, v_t_35_);
lean_dec_ref(v_cmp_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE___redArg(lean_object* v_cmp_37_, lean_object* v_t_38_, lean_object* v_k_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_37_, v_k_39_, v_t_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_cmp_43_, lean_object* v_inst_44_, lean_object* v_t_45_, lean_object* v_k_46_, lean_object* v_h_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_43_, v_k_46_, v_t_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT___redArg(lean_object* v_cmp_49_, lean_object* v_t_50_, lean_object* v_k_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_49_, v_k_51_, v_t_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_cmp_55_, lean_object* v_inst_56_, lean_object* v_t_57_, lean_object* v_k_58_, lean_object* v_h_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_55_, v_k_58_, v_t_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE___redArg(lean_object* v_cmp_61_, lean_object* v_t_62_, lean_object* v_k_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_61_, v_k_63_, v_t_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_cmp_67_, lean_object* v_inst_68_, lean_object* v_t_69_, lean_object* v_k_70_, lean_object* v_h_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_67_, v_k_70_, v_t_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT___redArg(lean_object* v_cmp_73_, lean_object* v_t_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_73_, v_k_75_, v_t_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_, lean_object* v_inst_80_, lean_object* v_t_81_, lean_object* v_k_82_, lean_object* v_h_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_79_, v_k_82_, v_t_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE___redArg(lean_object* v_cmp_85_, lean_object* v_t_86_, lean_object* v_k_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_85_, v_k_87_, v_t_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_, lean_object* v_inst_92_, lean_object* v_t_93_, lean_object* v_k_94_, lean_object* v_h_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_91_, v_k_94_, v_t_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT___redArg(lean_object* v_cmp_97_, lean_object* v_t_98_, lean_object* v_k_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_97_, v_k_99_, v_t_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_, lean_object* v_inst_104_, lean_object* v_t_105_, lean_object* v_k_106_, lean_object* v_h_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_103_, v_k_106_, v_t_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE___redArg(lean_object* v_cmp_109_, lean_object* v_t_110_, lean_object* v_k_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_109_, v_k_111_, v_t_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_cmp_115_, lean_object* v_inst_116_, lean_object* v_t_117_, lean_object* v_k_118_, lean_object* v_h_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_115_, v_k_118_, v_t_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT___redArg(lean_object* v_cmp_121_, lean_object* v_t_122_, lean_object* v_k_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_121_, v_k_123_, v_t_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_cmp_127_, lean_object* v_inst_128_, lean_object* v_t_129_, lean_object* v_k_130_, lean_object* v_h_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_127_, v_k_130_, v_t_129_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_133_, lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_133_, v_k_135_, v_t_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_137_, lean_object* v_cmp_138_, lean_object* v_00_u03b2_139_, lean_object* v_inst_140_, lean_object* v_t_141_, lean_object* v_k_142_, lean_object* v_h_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_138_, v_k_142_, v_t_141_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_145_, lean_object* v_t_146_, lean_object* v_k_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_145_, v_k_147_, v_t_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_149_, lean_object* v_cmp_150_, lean_object* v_00_u03b2_151_, lean_object* v_inst_152_, lean_object* v_t_153_, lean_object* v_k_154_, lean_object* v_h_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_150_, v_k_154_, v_t_153_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_157_, lean_object* v_t_158_, lean_object* v_k_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_157_, v_k_159_, v_t_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_161_, lean_object* v_cmp_162_, lean_object* v_00_u03b2_163_, lean_object* v_inst_164_, lean_object* v_t_165_, lean_object* v_k_166_, lean_object* v_h_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_162_, v_k_166_, v_t_165_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_169_, lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_169_, v_k_171_, v_t_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_173_, lean_object* v_cmp_174_, lean_object* v_00_u03b2_175_, lean_object* v_inst_176_, lean_object* v_t_177_, lean_object* v_k_178_, lean_object* v_h_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_174_, v_k_178_, v_t_177_);
return v___x_180_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
