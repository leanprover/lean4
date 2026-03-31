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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_m_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(v_00_u03b1_27_, v_m_28_, v_00_u03b2_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec_ref(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(lean_object* v_n_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v_zero_41_; uint8_t v_isZero_42_; 
v_zero_41_ = lean_unsigned_to_nat(0u);
v_isZero_42_ = lean_nat_dec_eq(v_n_38_, v_zero_41_);
if (v_isZero_42_ == 1)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_40_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__1_39_, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v_one_45_; lean_object* v_n_46_; lean_object* v___x_47_; 
lean_dec(v_h__1_39_);
v_one_45_ = lean_unsigned_to_nat(1u);
v_n_46_ = lean_nat_sub(v_n_38_, v_one_45_);
v___x_47_ = lean_apply_1(v_h__2_40_, v_n_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(lean_object* v_n_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_48_, v_h__1_49_, v_h__2_50_);
lean_dec(v_n_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(lean_object* v_motive_52_, lean_object* v_n_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
lean_object* v_zero_56_; uint8_t v_isZero_57_; 
v_zero_56_ = lean_unsigned_to_nat(0u);
v_isZero_57_ = lean_nat_dec_eq(v_n_53_, v_zero_56_);
if (v_isZero_57_ == 1)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_55_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__1_54_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v_one_60_; lean_object* v_n_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_54_);
v_one_60_ = lean_unsigned_to_nat(1u);
v_n_61_ = lean_nat_sub(v_n_53_, v_one_60_);
v___x_62_ = lean_apply_1(v_h__2_55_, v_n_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object* v_motive_63_, lean_object* v_n_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_63_, v_n_64_, v_h__1_65_, v_h__2_66_);
lean_dec(v_n_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v_it_72_; lean_object* v_out_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__2_70_);
v_it_72_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_it_72_);
v_out_73_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_out_73_);
lean_dec_ref(v_x_68_);
v___x_74_ = lean_apply_3(v_h__1_69_, v_it_72_, v_out_73_, lean_box(0));
return v___x_74_;
}
case 1:
{
lean_object* v_it_75_; lean_object* v___x_76_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__1_69_);
v_it_75_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_it_75_);
lean_dec_ref(v_x_68_);
v___x_76_ = lean_apply_2(v_h__2_70_, v_it_75_, lean_box(0));
return v___x_76_;
}
default: 
{
lean_object* v___x_77_; 
lean_dec(v_h__2_70_);
lean_dec(v_h__1_69_);
v___x_77_ = lean_apply_1(v_h__3_71_, lean_box(0));
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(lean_object* v_00_u03b1_78_, lean_object* v_m_79_, lean_object* v_00_u03b2_80_, lean_object* v_inst_81_, lean_object* v_it_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_object* v_it_88_; lean_object* v_out_89_; lean_object* v___x_90_; 
lean_dec(v_h__3_87_);
lean_dec(v_h__2_86_);
v_it_88_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_it_88_);
v_out_89_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_out_89_);
lean_dec_ref(v_x_84_);
v___x_90_ = lean_apply_3(v_h__1_85_, v_it_88_, v_out_89_, lean_box(0));
return v___x_90_;
}
case 1:
{
lean_object* v_it_91_; lean_object* v___x_92_; 
lean_dec(v_h__3_87_);
lean_dec(v_h__1_85_);
v_it_91_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_it_91_);
lean_dec_ref(v_x_84_);
v___x_92_ = lean_apply_2(v_h__2_86_, v_it_91_, lean_box(0));
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; 
lean_dec(v_h__2_86_);
lean_dec(v_h__1_85_);
v___x_93_ = lean_apply_1(v_h__3_87_, lean_box(0));
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_94_, lean_object* v_m_95_, lean_object* v_00_u03b2_96_, lean_object* v_inst_97_, lean_object* v_it_98_, lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_94_, v_m_95_, v_00_u03b2_96_, v_inst_97_, v_it_98_, v_motive_99_, v_x_100_, v_h__1_101_, v_h__2_102_, v_h__3_103_);
lean_dec(v_it_98_);
lean_dec(v_inst_97_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_){
_start:
{
switch(lean_obj_tag(v_x_105_))
{
case 0:
{
lean_object* v_it_109_; lean_object* v_out_110_; lean_object* v___x_111_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v_it_109_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_it_109_);
v_out_110_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_out_110_);
lean_dec_ref(v_x_105_);
v___x_111_ = lean_apply_2(v_h__1_106_, v_it_109_, v_out_110_);
return v___x_111_;
}
case 1:
{
lean_object* v_it_112_; lean_object* v___x_113_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__1_106_);
v_it_112_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_it_112_);
lean_dec_ref(v_x_105_);
v___x_113_ = lean_apply_1(v_h__2_107_, v_it_112_);
return v___x_113_;
}
default: 
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__3_108_, v___x_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_m_118_, lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_, lean_object* v_h__3_123_){
_start:
{
switch(lean_obj_tag(v_x_120_))
{
case 0:
{
lean_object* v_it_124_; lean_object* v_out_125_; lean_object* v___x_126_; 
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
v_it_124_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_it_124_);
v_out_125_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_out_125_);
lean_dec_ref(v_x_120_);
v___x_126_ = lean_apply_2(v_h__1_121_, v_it_124_, v_out_125_);
return v___x_126_;
}
case 1:
{
lean_object* v_it_127_; lean_object* v___x_128_; 
lean_dec(v_h__3_123_);
lean_dec(v_h__1_121_);
v_it_127_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_it_127_);
lean_dec_ref(v_x_120_);
v___x_128_ = lean_apply_1(v_h__2_122_, v_it_127_);
return v___x_128_;
}
default: 
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__3_123_, v___x_129_);
return v___x_130_;
}
}
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
