// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Append
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Append public import Init.Data.Iterators.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Monadic.Basic import Init.Data.List.Lemmas import Init.Data.List.ToArray
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(lean_object* v_m_11_, lean_object* v_00_u03b2_12_, lean_object* v_00_u03b1_u2081_13_, lean_object* v_inst_14_, lean_object* v_it_u2081_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(lean_object* v_m_27_, lean_object* v_00_u03b2_28_, lean_object* v_00_u03b1_u2081_29_, lean_object* v_inst_30_, lean_object* v_it_u2081_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(v_m_27_, v_00_u03b2_28_, v_00_u03b1_u2081_29_, v_inst_30_, v_it_u2081_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_u2081_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_, lean_object* v_h__3_41_){
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
v___x_44_ = lean_apply_3(v_h__1_39_, v_it_42_, v_out_43_, lean_box(0));
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
v___x_46_ = lean_apply_2(v_h__2_40_, v_it_45_, lean_box(0));
return v___x_46_;
}
default: 
{
lean_object* v___x_47_; 
lean_dec(v_h__2_40_);
lean_dec(v_h__1_39_);
v___x_47_ = lean_apply_1(v_h__3_41_, lean_box(0));
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(lean_object* v_00_u03b1_u2081_48_, lean_object* v_00_u03b2_49_, lean_object* v_m_50_, lean_object* v_inst_51_, lean_object* v_it_u2081_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
switch(lean_obj_tag(v_x_54_))
{
case 0:
{
lean_object* v_it_58_; lean_object* v_out_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v_it_58_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_it_58_);
v_out_59_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_out_59_);
lean_dec_ref(v_x_54_);
v___x_60_ = lean_apply_3(v_h__1_55_, v_it_58_, v_out_59_, lean_box(0));
return v___x_60_;
}
case 1:
{
lean_object* v_it_61_; lean_object* v___x_62_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__1_55_);
v_it_61_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_it_61_);
lean_dec_ref(v_x_54_);
v___x_62_ = lean_apply_2(v_h__2_56_, v_it_61_, lean_box(0));
return v___x_62_;
}
default: 
{
lean_object* v___x_63_; 
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
v___x_63_ = lean_apply_1(v_h__3_57_, lean_box(0));
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_64_, lean_object* v_00_u03b2_65_, lean_object* v_m_66_, lean_object* v_inst_67_, lean_object* v_it_u2081_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_, lean_object* v_h__3_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(v_00_u03b1_u2081_64_, v_00_u03b2_65_, v_m_66_, v_inst_67_, v_it_u2081_68_, v_motive_69_, v_x_70_, v_h__1_71_, v_h__2_72_, v_h__3_73_);
lean_dec(v_it_u2081_68_);
lean_dec(v_inst_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_object* v_it_79_; lean_object* v_out_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
v_it_79_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_it_79_);
v_out_80_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_out_80_);
lean_dec_ref(v_x_75_);
v___x_81_ = lean_apply_2(v_h__1_76_, v_it_79_, v_out_80_);
return v___x_81_;
}
case 1:
{
lean_object* v_it_82_; lean_object* v___x_83_; 
lean_dec(v_h__3_78_);
lean_dec(v_h__1_76_);
v_it_82_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_it_82_);
lean_dec_ref(v_x_75_);
v___x_83_ = lean_apply_1(v_h__2_77_, v_it_82_);
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_77_);
lean_dec(v_h__1_76_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__3_78_, v___x_84_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_m_88_, lean_object* v_motive_89_, lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_, lean_object* v_h__3_93_){
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
v___x_96_ = lean_apply_2(v_h__1_91_, v_it_94_, v_out_95_);
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
v___x_98_ = lean_apply_1(v_h__2_92_, v_it_97_);
return v___x_98_;
}
default: 
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_h__2_92_);
lean_dec(v_h__1_91_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_apply_1(v_h__3_93_, v___x_99_);
return v___x_100_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
}
#ifdef __cplusplus
}
#endif
