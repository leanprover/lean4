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
lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instCoeTypeForall__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_DTreeMap_instCoeTypeForall__2___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_instCoeTypeForall__2___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__2(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___redArg(lean_object* v_f_8_, lean_object* v_t_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_8_, v_t_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_00_u03b3_13_, lean_object* v_cmp_14_, lean_object* v_f_15_, lean_object* v_t_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_15_, v_t_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_filterMap___boxed(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_00_u03b3_20_, lean_object* v_cmp_21_, lean_object* v_f_22_, lean_object* v_t_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_DTreeMap_filterMap(v_00_u03b1_18_, v_00_u03b2_19_, v_00_u03b3_20_, v_cmp_21_, v_f_22_, v_t_23_);
lean_dec_ref(v_cmp_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___redArg(lean_object* v_f_25_, lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_00_u03b3_30_, lean_object* v_cmp_31_, lean_object* v_f_32_, lean_object* v_t_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_32_, v_t_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_map___boxed(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_00_u03b3_37_, lean_object* v_cmp_38_, lean_object* v_f_39_, lean_object* v_t_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_DTreeMap_map(v_00_u03b1_35_, v_00_u03b2_36_, v_00_u03b3_37_, v_cmp_38_, v_f_39_, v_t_40_);
lean_dec_ref(v_cmp_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE___redArg(lean_object* v_cmp_42_, lean_object* v_t_43_, lean_object* v_k_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_42_, v_k_44_, v_t_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGE(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_cmp_48_, lean_object* v_inst_49_, lean_object* v_t_50_, lean_object* v_k_51_, lean_object* v_h_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_48_, v_k_51_, v_t_50_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT___redArg(lean_object* v_cmp_54_, lean_object* v_t_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_54_, v_k_56_, v_t_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryGT(lean_object* v_00_u03b1_58_, lean_object* v_00_u03b2_59_, lean_object* v_cmp_60_, lean_object* v_inst_61_, lean_object* v_t_62_, lean_object* v_k_63_, lean_object* v_h_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_60_, v_k_63_, v_t_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE___redArg(lean_object* v_cmp_66_, lean_object* v_t_67_, lean_object* v_k_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_66_, v_k_68_, v_t_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLE(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_cmp_72_, lean_object* v_inst_73_, lean_object* v_t_74_, lean_object* v_k_75_, lean_object* v_h_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_72_, v_k_75_, v_t_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT___redArg(lean_object* v_cmp_78_, lean_object* v_t_79_, lean_object* v_k_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_78_, v_k_80_, v_t_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getEntryLT(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_, lean_object* v_inst_85_, lean_object* v_t_86_, lean_object* v_k_87_, lean_object* v_h_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_84_, v_k_87_, v_t_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE___redArg(lean_object* v_cmp_90_, lean_object* v_t_91_, lean_object* v_k_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_90_, v_k_92_, v_t_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGE(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_cmp_96_, lean_object* v_inst_97_, lean_object* v_t_98_, lean_object* v_k_99_, lean_object* v_h_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_96_, v_k_99_, v_t_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT___redArg(lean_object* v_cmp_102_, lean_object* v_t_103_, lean_object* v_k_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_102_, v_k_104_, v_t_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyGT(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_cmp_108_, lean_object* v_inst_109_, lean_object* v_t_110_, lean_object* v_k_111_, lean_object* v_h_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_108_, v_k_111_, v_t_110_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE___redArg(lean_object* v_cmp_114_, lean_object* v_t_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_114_, v_k_116_, v_t_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLE(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_cmp_120_, lean_object* v_inst_121_, lean_object* v_t_122_, lean_object* v_k_123_, lean_object* v_h_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_120_, v_k_123_, v_t_122_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT___redArg(lean_object* v_cmp_126_, lean_object* v_t_127_, lean_object* v_k_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_126_, v_k_128_, v_t_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_getKeyLT(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_cmp_132_, lean_object* v_inst_133_, lean_object* v_t_134_, lean_object* v_k_135_, lean_object* v_h_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_132_, v_k_135_, v_t_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE___redArg(lean_object* v_cmp_138_, lean_object* v_t_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_138_, v_k_140_, v_t_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGE(lean_object* v_00_u03b1_142_, lean_object* v_cmp_143_, lean_object* v_00_u03b2_144_, lean_object* v_inst_145_, lean_object* v_t_146_, lean_object* v_k_147_, lean_object* v_h_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_143_, v_k_147_, v_t_146_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT___redArg(lean_object* v_cmp_150_, lean_object* v_t_151_, lean_object* v_k_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_150_, v_k_152_, v_t_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryGT(lean_object* v_00_u03b1_154_, lean_object* v_cmp_155_, lean_object* v_00_u03b2_156_, lean_object* v_inst_157_, lean_object* v_t_158_, lean_object* v_k_159_, lean_object* v_h_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_155_, v_k_159_, v_t_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE___redArg(lean_object* v_cmp_162_, lean_object* v_t_163_, lean_object* v_k_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_162_, v_k_164_, v_t_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLE(lean_object* v_00_u03b1_166_, lean_object* v_cmp_167_, lean_object* v_00_u03b2_168_, lean_object* v_inst_169_, lean_object* v_t_170_, lean_object* v_k_171_, lean_object* v_h_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_167_, v_k_171_, v_t_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT___redArg(lean_object* v_cmp_174_, lean_object* v_t_175_, lean_object* v_k_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_174_, v_k_176_, v_t_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_getEntryLT(lean_object* v_00_u03b1_178_, lean_object* v_cmp_179_, lean_object* v_00_u03b2_180_, lean_object* v_inst_181_, lean_object* v_t_182_, lean_object* v_k_183_, lean_object* v_h_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_179_, v_k_183_, v_t_182_);
return v___x_185_;
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
