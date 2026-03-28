// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.ULift
// Imports: public import Init.Data.Iterators.Combinators.ULift import all Init.Data.Iterators.Combinators.ULift public import Init.Data.Iterators.Consumers.Collect public import Init.Data.Iterators.Consumers.Loop import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.Iterators.Lemmas.Consumers.Loop
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_m_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_27_, v_m_28_, v_00_u03b2_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_, lean_object* v_h__3_41_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_, lean_object* v_inst_50_, lean_object* v_it_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_){
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
v___x_59_ = lean_apply_3(v_h__1_54_, v_it_57_, v_out_58_, lean_box(0));
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
v___x_61_ = lean_apply_2(v_h__2_55_, v_it_60_, lean_box(0));
return v___x_61_;
}
default: 
{
lean_object* v___x_62_; 
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v___x_62_ = lean_apply_1(v_h__3_56_, lean_box(0));
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___boxed(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_inst_65_, lean_object* v_it_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(v_00_u03b1_63_, v_00_u03b2_64_, v_inst_65_, v_it_66_, v_motive_67_, v_x_68_, v_h__1_69_, v_h__2_70_, v_h__3_71_);
lean_dec(v_it_66_);
lean_dec(v_inst_65_);
return v_res_72_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
}
#ifdef __cplusplus
}
#endif
