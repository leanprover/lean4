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
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_DTreeMap_instCoeTypeForall__2___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___redArg(lean_object* v_f_7_, lean_object* v_t_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_7_, v_t_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_00_u03b3_12_, lean_object* v_cmp_13_, lean_object* v_f_14_, lean_object* v_t_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_14_, v_t_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_00_u03b3_19_, lean_object* v_cmp_20_, lean_object* v_f_21_, lean_object* v_t_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_DTreeMap_filterMap(v_00_u03b1_17_, v_00_u03b2_18_, v_00_u03b3_19_, v_cmp_20_, v_f_21_, v_t_22_);
lean_dec_ref(v_cmp_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___redArg(lean_object* v_f_24_, lean_object* v_t_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_24_, v_t_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_00_u03b3_29_, lean_object* v_cmp_30_, lean_object* v_f_31_, lean_object* v_t_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_31_, v_t_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_00_u03b3_36_, lean_object* v_cmp_37_, lean_object* v_f_38_, lean_object* v_t_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_DTreeMap_map(v_00_u03b1_34_, v_00_u03b2_35_, v_00_u03b3_36_, v_cmp_37_, v_f_38_, v_t_39_);
lean_dec_ref(v_cmp_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE___redArg(lean_object* v_cmp_41_, lean_object* v_t_42_, lean_object* v_k_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_41_, v_k_43_, v_t_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_cmp_47_, lean_object* v_inst_48_, lean_object* v_t_49_, lean_object* v_k_50_, lean_object* v_h_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_47_, v_k_50_, v_t_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT___redArg(lean_object* v_cmp_53_, lean_object* v_t_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_53_, v_k_55_, v_t_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_cmp_59_, lean_object* v_inst_60_, lean_object* v_t_61_, lean_object* v_k_62_, lean_object* v_h_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_59_, v_k_62_, v_t_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE___redArg(lean_object* v_cmp_65_, lean_object* v_t_66_, lean_object* v_k_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_65_, v_k_67_, v_t_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_cmp_71_, lean_object* v_inst_72_, lean_object* v_t_73_, lean_object* v_k_74_, lean_object* v_h_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_71_, v_k_74_, v_t_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT___redArg(lean_object* v_cmp_77_, lean_object* v_t_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_77_, v_k_79_, v_t_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_cmp_83_, lean_object* v_inst_84_, lean_object* v_t_85_, lean_object* v_k_86_, lean_object* v_h_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_83_, v_k_86_, v_t_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE___redArg(lean_object* v_cmp_89_, lean_object* v_t_90_, lean_object* v_k_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_89_, v_k_91_, v_t_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_, lean_object* v_inst_96_, lean_object* v_t_97_, lean_object* v_k_98_, lean_object* v_h_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_95_, v_k_98_, v_t_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT___redArg(lean_object* v_cmp_101_, lean_object* v_t_102_, lean_object* v_k_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_101_, v_k_103_, v_t_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_, lean_object* v_inst_108_, lean_object* v_t_109_, lean_object* v_k_110_, lean_object* v_h_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_107_, v_k_110_, v_t_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE___redArg(lean_object* v_cmp_113_, lean_object* v_t_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_113_, v_k_115_, v_t_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_, lean_object* v_inst_120_, lean_object* v_t_121_, lean_object* v_k_122_, lean_object* v_h_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_119_, v_k_122_, v_t_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT___redArg(lean_object* v_cmp_125_, lean_object* v_t_126_, lean_object* v_k_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_125_, v_k_127_, v_t_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_cmp_131_, lean_object* v_inst_132_, lean_object* v_t_133_, lean_object* v_k_134_, lean_object* v_h_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_131_, v_k_134_, v_t_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_137_, lean_object* v_t_138_, lean_object* v_k_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_137_, v_k_139_, v_t_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_141_, lean_object* v_cmp_142_, lean_object* v_00_u03b2_143_, lean_object* v_inst_144_, lean_object* v_t_145_, lean_object* v_k_146_, lean_object* v_h_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_142_, v_k_146_, v_t_145_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_149_, lean_object* v_t_150_, lean_object* v_k_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_149_, v_k_151_, v_t_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_153_, lean_object* v_cmp_154_, lean_object* v_00_u03b2_155_, lean_object* v_inst_156_, lean_object* v_t_157_, lean_object* v_k_158_, lean_object* v_h_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_154_, v_k_158_, v_t_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_161_, lean_object* v_t_162_, lean_object* v_k_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_161_, v_k_163_, v_t_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_165_, lean_object* v_cmp_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_t_169_, lean_object* v_k_170_, lean_object* v_h_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_166_, v_k_170_, v_t_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_173_, lean_object* v_t_174_, lean_object* v_k_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_173_, v_k_175_, v_t_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_177_, lean_object* v_cmp_178_, lean_object* v_00_u03b2_179_, lean_object* v_inst_180_, lean_object* v_t_181_, lean_object* v_k_182_, lean_object* v_h_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_178_, v_k_182_, v_t_181_);
return v___x_184_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
