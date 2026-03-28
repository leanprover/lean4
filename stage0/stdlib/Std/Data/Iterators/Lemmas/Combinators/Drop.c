// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Drop
// Imports: public import Std.Data.Iterators.Combinators.Drop public import Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop public import Init.Data.Iterators.Lemmas.Combinators.Take import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Access import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.Nat.TakeDrop import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_m_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(v_00_u03b1_27_, v_m_28_, v_00_u03b2_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(lean_object* v_n_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v_zero_41_; uint8_t v_isZero_42_; 
v_zero_41_ = lean_unsigned_to_nat(0u);
v_isZero_42_ = lean_nat_dec_eq(v_n_38_, v_zero_41_);
if (v_isZero_42_ == 1)
{
lean_object* v___x_43_; 
lean_dec(v_h__2_40_);
v___x_43_ = lean_apply_1(v_h__1_39_, lean_box(0));
return v___x_43_;
}
else
{
lean_object* v_one_44_; lean_object* v_n_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_39_);
v_one_44_ = lean_unsigned_to_nat(1u);
v_n_45_ = lean_nat_sub(v_n_38_, v_one_44_);
v___x_46_ = lean_apply_2(v_h__2_40_, v_n_45_, lean_box(0));
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg___boxed(lean_object* v_n_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(v_n_47_, v_h__1_48_, v_h__2_49_);
lean_dec(v_n_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(lean_object* v_motive_51_, lean_object* v_n_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v_zero_55_; uint8_t v_isZero_56_; 
v_zero_55_ = lean_unsigned_to_nat(0u);
v_isZero_56_ = lean_nat_dec_eq(v_n_52_, v_zero_55_);
if (v_isZero_56_ == 1)
{
lean_object* v___x_57_; 
lean_dec(v_h__2_54_);
v___x_57_ = lean_apply_1(v_h__1_53_, lean_box(0));
return v___x_57_;
}
else
{
lean_object* v_one_58_; lean_object* v_n_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_one_58_ = lean_unsigned_to_nat(1u);
v_n_59_ = lean_nat_sub(v_n_52_, v_one_58_);
v___x_60_ = lean_apply_2(v_h__2_54_, v_n_59_, lean_box(0));
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___boxed(lean_object* v_motive_61_, lean_object* v_n_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(v_motive_61_, v_n_62_, v_h__1_63_, v_h__2_64_);
lean_dec(v_n_62_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_, lean_object* v_h__3_69_){
_start:
{
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v_it_70_; lean_object* v_out_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__2_68_);
v_it_70_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_70_);
v_out_71_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_out_71_);
lean_dec_ref(v_x_66_);
v___x_72_ = lean_apply_3(v_h__1_67_, v_it_70_, v_out_71_, lean_box(0));
return v___x_72_;
}
case 1:
{
lean_object* v_it_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__1_67_);
v_it_73_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_73_);
lean_dec_ref(v_x_66_);
v___x_74_ = lean_apply_2(v_h__2_68_, v_it_73_, lean_box(0));
return v___x_74_;
}
default: 
{
lean_object* v___x_75_; 
lean_dec(v_h__2_68_);
lean_dec(v_h__1_67_);
v___x_75_ = lean_apply_1(v_h__3_69_, lean_box(0));
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_it_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_object* v_it_85_; lean_object* v_out_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v_it_85_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_85_);
v_out_86_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_out_86_);
lean_dec_ref(v_x_81_);
v___x_87_ = lean_apply_3(v_h__1_82_, v_it_85_, v_out_86_, lean_box(0));
return v___x_87_;
}
case 1:
{
lean_object* v_it_88_; lean_object* v___x_89_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__1_82_);
v_it_88_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_88_);
lean_dec_ref(v_x_81_);
v___x_89_ = lean_apply_2(v_h__2_83_, v_it_88_, lean_box(0));
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; 
lean_dec(v_h__2_83_);
lean_dec(v_h__1_82_);
v___x_90_ = lean_apply_1(v_h__3_84_, lean_box(0));
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_it_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(v_00_u03b1_91_, v_00_u03b2_92_, v_inst_93_, v_it_94_, v_motive_95_, v_x_96_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
lean_dec(v_it_94_);
lean_dec(v_inst_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(lean_object* v_n_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v_zero_104_; uint8_t v_isZero_105_; 
v_zero_104_ = lean_unsigned_to_nat(0u);
v_isZero_105_ = lean_nat_dec_eq(v_n_101_, v_zero_104_);
if (v_isZero_105_ == 1)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_103_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_apply_1(v_h__1_102_, v___x_106_);
return v___x_107_;
}
else
{
lean_object* v_one_108_; lean_object* v_n_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_102_);
v_one_108_ = lean_unsigned_to_nat(1u);
v_n_109_ = lean_nat_sub(v_n_101_, v_one_108_);
v___x_110_ = lean_apply_1(v_h__2_103_, v_n_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg___boxed(lean_object* v_n_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(v_n_111_, v_h__1_112_, v_h__2_113_);
lean_dec(v_n_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(lean_object* v_motive_115_, lean_object* v_n_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
lean_object* v_zero_119_; uint8_t v_isZero_120_; 
v_zero_119_ = lean_unsigned_to_nat(0u);
v_isZero_120_ = lean_nat_dec_eq(v_n_116_, v_zero_119_);
if (v_isZero_120_ == 1)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__2_118_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__1_117_, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_one_123_; lean_object* v_n_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_117_);
v_one_123_ = lean_unsigned_to_nat(1u);
v_n_124_ = lean_nat_sub(v_n_116_, v_one_123_);
v___x_125_ = lean_apply_1(v_h__2_118_, v_n_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___boxed(lean_object* v_motive_126_, lean_object* v_n_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(v_motive_126_, v_n_127_, v_h__1_128_, v_h__2_129_);
lean_dec(v_n_127_);
return v_res_130_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Drop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Drop(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
}
#ifdef __cplusplus
}
#endif
