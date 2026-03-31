// Lean compiler output
// Module: Init.Control.Lawful.Instances
// Imports: public import Init.Control.Lawful.Basic import all Init.Control.Except public import Init.Control.Option import all Init.Control.Option import all Init.Control.State public import Init.Control.StateRef public import Init.Control.State public import Init.Ext
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
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref(v_x_1_);
v___x_5_ = lean_apply_1(v_h__2_3_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_8_, lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v_a_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_x_11_);
v___x_15_ = lean_apply_1(v_h__2_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_a_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_x_11_);
v___x_17_ = lean_apply_1(v_h__1_12_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v_a_21_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref(v_x_18_);
v___x_22_ = lean_apply_1(v_h__2_20_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_a_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v_x_18_);
v___x_24_ = lean_apply_1(v_h__1_19_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_25_, lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_29_);
v_a_31_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_x_28_);
v___x_32_ = lean_apply_1(v_h__2_30_, v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_30_);
v_a_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v_x_28_);
v___x_34_ = lean_apply_1(v_h__1_29_, v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_____do__lift_35_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__2_37_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_val_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v_val_40_ = lean_ctor_get(v_____do__lift_35_, 0);
lean_inc(v_val_40_);
lean_dec_ref(v_____do__lift_35_);
v___x_41_ = lean_apply_1(v_h__1_36_, v_val_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_____do__lift_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_____do__lift_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__2_46_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_val_49_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_____do__lift_44_);
v___x_50_ = lean_apply_1(v_h__1_45_, v_val_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_opt_51_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_52_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__2_53_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_53_);
v_val_56_ = lean_ctor_get(v_opt_51_, 0);
lean_inc(v_val_56_);
lean_dec_ref(v_opt_51_);
v___x_57_ = lean_apply_1(v_h__1_52_, v_val_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_opt_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_opt_60_) == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_61_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_apply_1(v_h__2_62_, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v___x_66_; 
lean_dec(v_h__2_62_);
v_val_65_ = lean_ctor_get(v_opt_60_, 0);
lean_inc(v_val_65_);
lean_dec_ref(v_opt_60_);
v___x_66_ = lean_apply_1(v_h__1_61_, v_val_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_72_; 
lean_dec(v_h__1_70_);
v___x_72_ = lean_apply_2(v_h__2_71_, v_x_68_, v_x_69_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_71_);
v_val_73_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v_x_67_);
v___x_74_ = lean_apply_3(v_h__1_70_, v_val_73_, v_x_68_, v_x_69_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__1_81_);
v___x_83_ = lean_apply_2(v_h__2_82_, v_x_79_, v_x_80_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_82_);
v_val_84_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_84_);
lean_dec_ref(v_x_78_);
v___x_85_ = lean_apply_3(v_h__1_81_, v_val_84_, v_x_79_, v_x_80_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_87_);
v_a_89_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_a_90_);
lean_dec_ref(v_x_86_);
v___x_91_ = lean_apply_2(v_h__2_88_, v_a_89_, v_a_90_);
return v___x_91_;
}
else
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__2_88_);
v_a_92_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_a_93_);
lean_dec_ref(v_x_86_);
v___x_94_ = lean_apply_2(v_h__1_87_, v_a_92_, v_a_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_95_, lean_object* v_00_u03c3_96_, lean_object* v_00_u03b1_97_, lean_object* v_motive_98_, lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_a_102_; lean_object* v_a_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_100_);
v_a_102_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_a_102_);
v_a_103_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_a_103_);
lean_dec_ref(v_x_99_);
v___x_104_ = lean_apply_2(v_h__2_101_, v_a_102_, v_a_103_);
return v___x_104_;
}
else
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_101_);
v_a_105_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_a_105_);
v_a_106_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_a_106_);
lean_dec_ref(v_x_99_);
v___x_107_ = lean_apply_2(v_h__1_100_, v_a_105_, v_a_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_a_111_; lean_object* v_a_112_; lean_object* v___x_113_; 
lean_dec(v_h__2_110_);
v_a_111_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_a_111_);
v_a_112_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_a_112_);
lean_dec_ref(v_x_108_);
v___x_113_ = lean_apply_2(v_h__1_109_, v_a_111_, v_a_112_);
return v___x_113_;
}
else
{
lean_object* v_a_114_; lean_object* v_a_115_; lean_object* v___x_116_; 
lean_dec(v_h__1_109_);
v_a_114_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_a_114_);
v_a_115_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_a_115_);
lean_dec_ref(v_x_108_);
v___x_116_ = lean_apply_2(v_h__2_110_, v_a_114_, v_a_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_117_, lean_object* v_00_u03c3_118_, lean_object* v_00_u03b1_119_, lean_object* v_motive_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_123_);
v_a_124_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_a_124_);
v_a_125_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_a_125_);
lean_dec_ref(v_x_121_);
v___x_126_ = lean_apply_2(v_h__1_122_, v_a_124_, v_a_125_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_129_; 
lean_dec(v_h__1_122_);
v_a_127_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_a_127_);
v_a_128_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_a_128_);
lean_dec_ref(v_x_121_);
v___x_129_ = lean_apply_2(v_h__2_123_, v_a_127_, v_a_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter___redArg(lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v_a_133_; lean_object* v_a_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_132_);
v_a_133_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_a_133_);
v_a_134_ = lean_ctor_get(v_x_130_, 1);
lean_inc(v_a_134_);
lean_dec_ref(v_x_130_);
v___x_135_ = lean_apply_2(v_h__1_131_, v_a_133_, v_a_134_);
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_138_; 
lean_dec(v_h__1_131_);
v_a_136_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_a_136_);
v_a_137_ = lean_ctor_get(v_x_130_, 1);
lean_inc(v_a_137_);
lean_dec_ref(v_x_130_);
v___x_138_ = lean_apply_2(v_h__2_132_, v_a_136_, v_a_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter(lean_object* v_00_u03b5_139_, lean_object* v_00_u03c3_140_, lean_object* v_00_u03b1_141_, lean_object* v_motive_142_, lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v_a_146_; lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_145_);
v_a_146_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_a_146_);
v_a_147_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_a_147_);
lean_dec_ref(v_x_143_);
v___x_148_ = lean_apply_2(v_h__1_144_, v_a_146_, v_a_147_);
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v_a_150_; lean_object* v___x_151_; 
lean_dec(v_h__1_144_);
v_a_149_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_a_149_);
v_a_150_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_a_150_);
lean_dec_ref(v_x_143_);
v___x_151_ = lean_apply_2(v_h__2_145_, v_a_149_, v_a_150_);
return v___x_151_;
}
}
}
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Lawful_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Lawful_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Lawful_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Lawful_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Lawful_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
