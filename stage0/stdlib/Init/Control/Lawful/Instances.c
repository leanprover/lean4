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
lean_object* v___x_14_; 
v___x_14_ = l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(v_x_11_, v_h__1_12_, v_h__2_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_16_);
v_a_18_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_a_18_);
lean_dec_ref(v_x_15_);
v___x_19_ = lean_apply_1(v_h__2_17_, v_a_18_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_17_);
v_a_20_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_x_15_);
v___x_21_ = lean_apply_1(v_h__1_16_, v_a_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_22_, lean_object* v_00_u03b1_23_, lean_object* v_motive_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter___redArg(v_x_25_, v_h__1_26_, v_h__2_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_____do__lift_29_) == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_30_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_apply_1(v_h__2_31_, v___x_32_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_31_);
v_val_34_ = lean_ctor_get(v_____do__lift_29_, 0);
lean_inc(v_val_34_);
lean_dec_ref(v_____do__lift_29_);
v___x_35_ = lean_apply_1(v_h__1_30_, v_val_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_36_, lean_object* v_motive_37_, lean_object* v_____do__lift_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter___redArg(v_____do__lift_38_, v_h__1_39_, v_h__2_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_opt_42_) == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_43_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_apply_1(v_h__2_44_, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_44_);
v_val_47_ = lean_ctor_get(v_opt_42_, 0);
lean_inc(v_val_47_);
lean_dec_ref(v_opt_42_);
v___x_48_ = lean_apply_1(v_h__1_43_, v_val_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_49_, lean_object* v_motive_50_, lean_object* v_opt_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter___redArg(v_opt_51_, v_h__1_52_, v_h__2_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter___redArg(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_60_; 
lean_dec(v_h__1_58_);
v___x_60_ = lean_apply_2(v_h__2_59_, v_x_56_, v_x_57_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_59_);
v_val_61_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_61_);
lean_dec_ref(v_x_55_);
v___x_62_ = lean_apply_3(v_h__1_58_, v_val_61_, v_x_56_, v_x_57_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_motive_65_, lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter___redArg(v_x_66_, v_x_67_, v_x_68_, v_h__1_69_, v_h__2_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_a_75_; lean_object* v_a_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_73_);
v_a_75_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_a_75_);
v_a_76_ = lean_ctor_get(v_x_72_, 1);
lean_inc(v_a_76_);
lean_dec_ref(v_x_72_);
v___x_77_ = lean_apply_2(v_h__2_74_, v_a_75_, v_a_76_);
return v___x_77_;
}
else
{
lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_h__2_74_);
v_a_78_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_a_78_);
v_a_79_ = lean_ctor_get(v_x_72_, 1);
lean_inc(v_a_79_);
lean_dec_ref(v_x_72_);
v___x_80_ = lean_apply_2(v_h__1_73_, v_a_78_, v_a_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_81_, lean_object* v_00_u03c3_82_, lean_object* v_00_u03b1_83_, lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter___redArg(v_x_85_, v_h__1_86_, v_h__2_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__2_91_);
v_a_92_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_a_93_);
lean_dec_ref(v_x_89_);
v___x_94_ = lean_apply_2(v_h__1_90_, v_a_92_, v_a_93_);
return v___x_94_;
}
else
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; 
lean_dec(v_h__1_90_);
v_a_95_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_a_96_);
lean_dec_ref(v_x_89_);
v___x_97_ = lean_apply_2(v_h__2_91_, v_a_95_, v_a_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_98_, lean_object* v_00_u03c3_99_, lean_object* v_00_u03b1_100_, lean_object* v_motive_101_, lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter___redArg(v_x_102_, v_h__1_103_, v_h__2_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter___redArg(lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_108_);
v_a_109_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_a_109_);
v_a_110_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_a_110_);
lean_dec_ref(v_x_106_);
v___x_111_ = lean_apply_2(v_h__1_107_, v_a_109_, v_a_110_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_114_; 
lean_dec(v_h__1_107_);
v_a_112_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_a_112_);
v_a_113_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_a_113_);
lean_dec_ref(v_x_106_);
v___x_114_ = lean_apply_2(v_h__2_108_, v_a_112_, v_a_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter(lean_object* v_00_u03b5_115_, lean_object* v_00_u03c3_116_, lean_object* v_00_u03b1_117_, lean_object* v_motive_118_, lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter___redArg(v_x_119_, v_h__1_120_, v_h__2_121_);
return v___x_122_;
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
