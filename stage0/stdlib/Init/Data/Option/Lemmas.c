// Lean compiler output
// Module: Init.Data.Option.Lemmas
// Imports: import all Init.Data.Option.BasicAux public import Init.Data.Option.Instances import all Init.Data.Option.Instances public import Init.Ext public import Init.Data.Option.BasicAux public import Init.PropLemmas import Init.Classical import Init.Data.BEq import Init.Data.Bool
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_18_; 
lean_dec(v_h__2_17_);
v___x_18_ = lean_apply_1(v_h__1_16_, v_x_15_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_16_);
v_val_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_19_);
lean_dec_ref(v_x_14_);
v___x_20_ = lean_apply_2(v_h__2_17_, v_val_19_, v_x_15_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(v_x_24_, v_x_25_, v_h__1_26_, v_h__2_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_, lean_object* v_h__3_33_, lean_object* v_h__4_34_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_dec(v_h__4_34_);
lean_dec(v_h__2_32_);
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__3_33_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_31_, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_31_);
v_val_37_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v_x_30_);
v___x_38_ = lean_apply_1(v_h__3_33_, v_val_37_);
return v___x_38_;
}
}
else
{
lean_dec(v_h__3_33_);
lean_dec(v_h__1_31_);
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v_val_39_; lean_object* v___x_40_; 
lean_dec(v_h__4_34_);
v_val_39_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_val_39_);
lean_dec_ref(v_x_29_);
v___x_40_ = lean_apply_1(v_h__2_32_, v_val_39_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_32_);
v_val_41_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_val_41_);
lean_dec_ref(v_x_29_);
v_val_42_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_x_30_);
v___x_43_ = lean_apply_2(v_h__4_34_, v_val_41_, v_val_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_, lean_object* v_h__4_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(v_x_46_, v_x_47_, v_h__1_48_, v_h__2_49_, v_h__3_50_, v_h__4_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_57_; 
lean_dec(v_h__1_55_);
v___x_57_ = lean_apply_1(v_h__2_56_, v_x_54_);
return v___x_57_;
}
else
{
lean_object* v_val_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_56_);
v_val_58_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_val_58_);
lean_dec_ref(v_x_53_);
v___x_59_ = lean_apply_2(v_h__1_55_, v_val_58_, v_x_54_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(v_x_62_, v_x_63_, v_h__1_64_, v_h__2_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_70_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_apply_1(v_h__1_68_, lean_box(0));
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_68_);
v_val_71_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_x_67_);
v___x_72_ = lean_apply_2(v_h__2_69_, v_val_71_, lean_box(0));
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(lean_object* v_00_u03b1_73_, lean_object* v_p_74_, lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(v_x_76_, v_h__1_78_, v_h__2_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(lean_object* v_o_81_, lean_object* v_p_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_o_81_) == 0)
{
lean_object* v___x_85_; 
lean_dec(v_h__2_84_);
v___x_85_ = lean_apply_1(v_h__1_83_, v_p_82_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_83_);
v_val_86_ = lean_ctor_get(v_o_81_, 0);
lean_inc(v_val_86_);
lean_dec_ref(v_o_81_);
v___x_87_ = lean_apply_2(v_h__2_84_, v_val_86_, v_p_82_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(lean_object* v_00_u03b1_88_, lean_object* v_motive_89_, lean_object* v_o_90_, lean_object* v_p_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(v_o_90_, v_p_91_, v_h__1_92_, v_h__2_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_dec(v_h__2_98_);
if (lean_obj_tag(v_x_96_) == 1)
{
lean_object* v_val_100_; lean_object* v___x_101_; 
lean_dec(v_h__3_99_);
v_val_100_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_100_);
lean_dec_ref(v_x_96_);
v___x_101_ = lean_apply_1(v_h__1_97_, v_val_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
lean_dec(v_h__1_97_);
v___x_102_ = lean_apply_4(v_h__3_99_, v_x_95_, v_x_96_, lean_box(0), lean_box(0));
return v___x_102_;
}
}
else
{
lean_dec(v_h__1_97_);
if (lean_obj_tag(v_x_96_) == 1)
{
lean_object* v_val_103_; lean_object* v_val_104_; lean_object* v___x_105_; 
lean_dec(v_h__3_99_);
v_val_103_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_val_103_);
lean_dec_ref(v_x_95_);
v_val_104_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_104_);
lean_dec_ref(v_x_96_);
v___x_105_ = lean_apply_2(v_h__2_98_, v_val_103_, v_val_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; 
lean_dec(v_h__2_98_);
v___x_106_ = lean_apply_4(v_h__3_99_, v_x_95_, v_x_96_, lean_box(0), lean_box(0));
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_dec(v_h__2_113_);
if (lean_obj_tag(v_x_111_) == 1)
{
lean_object* v_val_115_; lean_object* v___x_116_; 
lean_dec(v_h__3_114_);
v_val_115_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_val_115_);
lean_dec_ref(v_x_111_);
v___x_116_ = lean_apply_1(v_h__1_112_, v_val_115_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
lean_dec(v_h__1_112_);
v___x_117_ = lean_apply_4(v_h__3_114_, v_x_110_, v_x_111_, lean_box(0), lean_box(0));
return v___x_117_;
}
}
else
{
lean_dec(v_h__1_112_);
if (lean_obj_tag(v_x_111_) == 1)
{
lean_object* v_val_118_; lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__3_114_);
v_val_118_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v_x_110_);
v_val_119_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_x_111_);
v___x_120_ = lean_apply_2(v_h__2_113_, v_val_118_, v_val_119_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__2_113_);
v___x_121_ = lean_apply_4(v_h__3_114_, v_x_110_, v_x_111_, lean_box(0), lean_box(0));
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_, lean_object* v_h__3_126_, lean_object* v_h__4_127_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_dec(v_h__4_127_);
lean_dec(v_h__3_126_);
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__1_124_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__2_125_, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v_val_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_125_);
v_val_130_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_val_130_);
lean_dec_ref(v_x_123_);
v___x_131_ = lean_apply_1(v_h__1_124_, v_val_130_);
return v___x_131_;
}
}
else
{
lean_dec(v_h__2_125_);
lean_dec(v_h__1_124_);
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v_val_132_; lean_object* v___x_133_; 
lean_dec(v_h__4_127_);
v_val_132_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_val_132_);
lean_dec_ref(v_x_122_);
v___x_133_ = lean_apply_1(v_h__3_126_, v_val_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__3_126_);
v_val_134_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v_x_122_);
v_val_135_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v_x_123_);
v___x_136_ = lean_apply_2(v_h__4_127_, v_val_134_, v_val_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_motive_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_, lean_object* v_h__3_144_, lean_object* v_h__4_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(v_x_140_, v_x_141_, v_h__1_142_, v_h__2_143_, v_h__3_144_, v_h__4_145_);
return v___x_146_;
}
}
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
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
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
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
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
