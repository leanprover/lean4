// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Take public import Init.Data.Iterators.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Monadic.Basic import Init.Data.Nat.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_m_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_it_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(v_00_u03b1_22_, v_m_23_, v_00_u03b2_24_, v_inst_25_, v_it_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec_ref(v_it_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(lean_object* v_n_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_n_33_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_34_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_one_40_; lean_object* v_n_41_; lean_object* v___x_42_; 
lean_dec(v_h__1_34_);
v_one_40_ = lean_unsigned_to_nat(1u);
v_n_41_ = lean_nat_sub(v_n_33_, v_one_40_);
v___x_42_ = lean_apply_1(v_h__2_35_, v_n_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(lean_object* v_n_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_43_, v_h__1_44_, v_h__2_45_);
lean_dec(v_n_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(lean_object* v_motive_47_, lean_object* v_n_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_48_, v_h__1_49_, v_h__2_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object* v_motive_52_, lean_object* v_n_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_52_, v_n_53_, v_h__1_54_, v_h__2_55_);
lean_dec(v_n_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_, lean_object* v_h__3_60_){
_start:
{
switch(lean_obj_tag(v_x_57_))
{
case 0:
{
lean_object* v_it_61_; lean_object* v_out_62_; lean_object* v___x_63_; 
lean_dec(v_h__3_60_);
lean_dec(v_h__2_59_);
v_it_61_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_it_61_);
v_out_62_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_out_62_);
lean_dec_ref(v_x_57_);
v___x_63_ = lean_apply_3(v_h__1_58_, v_it_61_, v_out_62_, lean_box(0));
return v___x_63_;
}
case 1:
{
lean_object* v_it_64_; lean_object* v___x_65_; 
lean_dec(v_h__3_60_);
lean_dec(v_h__1_58_);
v_it_64_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_it_64_);
lean_dec_ref(v_x_57_);
v___x_65_ = lean_apply_2(v_h__2_59_, v_it_64_, lean_box(0));
return v___x_65_;
}
default: 
{
lean_object* v___x_66_; 
lean_dec(v_h__2_59_);
lean_dec(v_h__1_58_);
v___x_66_ = lean_apply_1(v_h__3_60_, lean_box(0));
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(lean_object* v_00_u03b1_67_, lean_object* v_m_68_, lean_object* v_00_u03b2_69_, lean_object* v_inst_70_, lean_object* v_it_71_, lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(v_x_73_, v_h__1_74_, v_h__2_75_, v_h__3_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_78_, lean_object* v_m_79_, lean_object* v_00_u03b2_80_, lean_object* v_inst_81_, lean_object* v_it_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_78_, v_m_79_, v_00_u03b2_80_, v_inst_81_, v_it_82_, v_motive_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_it_82_);
lean_dec(v_inst_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
lean_object* v_it_93_; lean_object* v_out_94_; lean_object* v___x_95_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
v_it_93_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_93_);
v_out_94_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_out_94_);
lean_dec_ref(v_x_89_);
v___x_95_ = lean_apply_2(v_h__1_90_, v_it_93_, v_out_94_);
return v___x_95_;
}
case 1:
{
lean_object* v_it_96_; lean_object* v___x_97_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__1_90_);
v_it_96_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_96_);
lean_dec_ref(v_x_89_);
v___x_97_ = lean_apply_1(v_h__2_91_, v_it_96_);
return v___x_97_;
}
default: 
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_apply_1(v_h__3_92_, v___x_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_m_102_, lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_, lean_object* v_h__3_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_104_, v_h__1_105_, v_h__2_106_, v_h__3_107_);
return v___x_108_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
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
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
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
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
}
#ifdef __cplusplus
}
#endif
