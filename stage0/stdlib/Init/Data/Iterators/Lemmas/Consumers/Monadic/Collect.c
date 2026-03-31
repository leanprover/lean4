// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Collect import all Init.Data.Iterators.Consumers.Monadic.Collect import all Init.Data.Iterators.Consumers.Monadic.Total import all Init.WFExtrinsicFix public import Init.Control.Lawful import Init.Data.Array.Bootstrap import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Monadic.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_it_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_3(v_h__1_2_, v_it_5_, v_out_6_, lean_box(0));
return v___x_7_;
}
case 1:
{
lean_object* v_it_8_; lean_object* v___x_9_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_it_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_it_8_, lean_box(0));
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_apply_1(v_h__3_4_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_m_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
switch(lean_obj_tag(v_x_17_))
{
case 0:
{
lean_object* v_it_21_; lean_object* v_out_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v_it_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_21_);
v_out_22_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_out_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_3(v_h__1_18_, v_it_21_, v_out_22_, lean_box(0));
return v___x_23_;
}
case 1:
{
lean_object* v_it_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__1_18_);
v_it_24_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_24_);
lean_dec_ref(v_x_17_);
v___x_25_ = lean_apply_2(v_h__2_19_, v_it_24_, lean_box(0));
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; 
lean_dec(v_h__2_19_);
lean_dec(v_h__1_18_);
v___x_26_ = lean_apply_1(v_h__3_20_, lean_box(0));
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_m_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(v_00_u03b1_27_, v_00_u03b2_28_, v_m_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_, lean_object* v_h__3_41_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
lean_object* v_it_42_; lean_object* v_out_43_; lean_object* v___x_44_; 
lean_dec(v_h__3_41_);
lean_dec(v_h__2_40_);
v_it_42_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_it_42_);
v_out_43_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_out_43_);
lean_dec_ref(v_x_38_);
v___x_44_ = lean_apply_2(v_h__1_39_, v_it_42_, v_out_43_);
return v___x_44_;
}
case 1:
{
lean_object* v_it_45_; lean_object* v___x_46_; 
lean_dec(v_h__3_41_);
lean_dec(v_h__1_39_);
v_it_45_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_it_45_);
lean_dec_ref(v_x_38_);
v___x_46_ = lean_apply_1(v_h__2_40_, v_it_45_);
return v___x_46_;
}
default: 
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_40_);
lean_dec(v_h__1_39_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__3_41_, v___x_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_m_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_){
_start:
{
switch(lean_obj_tag(v_x_53_))
{
case 0:
{
lean_object* v_it_57_; lean_object* v_out_58_; lean_object* v___x_59_; 
lean_dec(v_h__3_56_);
lean_dec(v_h__2_55_);
v_it_57_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_it_57_);
v_out_58_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_out_58_);
lean_dec_ref(v_x_53_);
v___x_59_ = lean_apply_2(v_h__1_54_, v_it_57_, v_out_58_);
return v___x_59_;
}
case 1:
{
lean_object* v_it_60_; lean_object* v___x_61_; 
lean_dec(v_h__3_56_);
lean_dec(v_h__1_54_);
v_it_60_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_it_60_);
lean_dec_ref(v_x_53_);
v___x_61_ = lean_apply_1(v_h__2_55_, v_it_60_);
return v___x_61_;
}
default: 
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__3_56_, v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_, lean_object* v_h__3_67_){
_start:
{
switch(lean_obj_tag(v_x_64_))
{
case 0:
{
lean_object* v_it_68_; lean_object* v_out_69_; lean_object* v___x_70_; 
lean_dec(v_h__3_67_);
lean_dec(v_h__2_66_);
v_it_68_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_it_68_);
v_out_69_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_out_69_);
lean_dec_ref(v_x_64_);
v___x_70_ = lean_apply_2(v_h__1_65_, v_it_68_, v_out_69_);
return v___x_70_;
}
case 1:
{
lean_object* v_it_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_67_);
lean_dec(v_h__1_65_);
v_it_71_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_it_71_);
lean_dec_ref(v_x_64_);
v___x_72_ = lean_apply_1(v_h__2_66_, v_it_71_);
return v___x_72_;
}
default: 
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_66_);
lean_dec(v_h__1_65_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__3_67_, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_m_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_, lean_object* v_h__3_82_){
_start:
{
switch(lean_obj_tag(v_x_79_))
{
case 0:
{
lean_object* v_it_83_; lean_object* v_out_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_82_);
lean_dec(v_h__2_81_);
v_it_83_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_it_83_);
v_out_84_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_out_84_);
lean_dec_ref(v_x_79_);
v___x_85_ = lean_apply_2(v_h__1_80_, v_it_83_, v_out_84_);
return v___x_85_;
}
case 1:
{
lean_object* v_it_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_82_);
lean_dec(v_h__1_80_);
v_it_86_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_it_86_);
lean_dec_ref(v_x_79_);
v___x_87_ = lean_apply_1(v_h__2_81_, v_it_86_);
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_81_);
lean_dec(v_h__1_80_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__3_82_, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___redArg(lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_, lean_object* v_h__3_93_){
_start:
{
switch(lean_obj_tag(v_x_90_))
{
case 0:
{
lean_object* v_it_94_; lean_object* v_out_95_; lean_object* v___x_96_; 
lean_dec(v_h__3_93_);
lean_dec(v_h__2_92_);
v_it_94_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_it_94_);
v_out_95_ = lean_ctor_get(v_x_90_, 1);
lean_inc(v_out_95_);
lean_dec_ref(v_x_90_);
v___x_96_ = lean_apply_3(v_h__1_91_, v_it_94_, v_out_95_, lean_box(0));
return v___x_96_;
}
case 1:
{
lean_object* v_it_97_; lean_object* v___x_98_; 
lean_dec(v_h__3_93_);
lean_dec(v_h__1_91_);
v_it_97_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_it_97_);
lean_dec_ref(v_x_90_);
v___x_98_ = lean_apply_2(v_h__2_92_, v_it_97_, lean_box(0));
return v___x_98_;
}
default: 
{
lean_object* v___x_99_; 
lean_dec(v_h__2_92_);
lean_dec(v_h__1_91_);
v___x_99_ = lean_apply_1(v_h__3_93_, lean_box(0));
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(lean_object* v_00_u03b1_100_, lean_object* v_m_101_, lean_object* v_00_u03b2_102_, lean_object* v_inst_103_, lean_object* v_it_104_, lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_, lean_object* v_h__3_109_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
lean_object* v_it_110_; lean_object* v_out_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_109_);
lean_dec(v_h__2_108_);
v_it_110_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_it_110_);
v_out_111_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_out_111_);
lean_dec_ref(v_x_106_);
v___x_112_ = lean_apply_3(v_h__1_107_, v_it_110_, v_out_111_, lean_box(0));
return v___x_112_;
}
case 1:
{
lean_object* v_it_113_; lean_object* v___x_114_; 
lean_dec(v_h__3_109_);
lean_dec(v_h__1_107_);
v_it_113_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_it_113_);
lean_dec_ref(v_x_106_);
v___x_114_ = lean_apply_2(v_h__2_108_, v_it_113_, lean_box(0));
return v___x_114_;
}
default: 
{
lean_object* v___x_115_; 
lean_dec(v_h__2_108_);
lean_dec(v_h__1_107_);
v___x_115_ = lean_apply_1(v_h__3_109_, lean_box(0));
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___boxed(lean_object* v_00_u03b1_116_, lean_object* v_m_117_, lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_it_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_, lean_object* v_h__3_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(v_00_u03b1_116_, v_m_117_, v_00_u03b2_118_, v_inst_119_, v_it_120_, v_motive_121_, v_x_122_, v_h__1_123_, v_h__2_124_, v_h__3_125_);
lean_dec(v_it_120_);
lean_dec(v_inst_119_);
return v_res_126_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
}
#ifdef __cplusplus
}
#endif
