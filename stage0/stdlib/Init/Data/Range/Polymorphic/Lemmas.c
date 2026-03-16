// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Lemmas
// Imports: import Init.Data.Iterators.Lemmas.Consumers.Collect import all Init.Data.Range.Polymorphic.Basic import all Init.Data.Range.Polymorphic.RangeIterator public import Init.Data.Range.Polymorphic.Iterators import all Init.Data.Range.Polymorphic.Iterators import all Init.Data.Iterators.Consumers.Loop import Init.Data.Array.Monadic public import Init.Data.List.Control public import Init.Data.Order.Lemmas import Init.Data.Array.Bootstrap import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Loop import Init.Data.List.Pairwise import Init.Data.Nat.Linear import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_16_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__1_15_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v_val_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_19_);
lean_dec_ref(v_x_14_);
v___x_20_ = lean_apply_1(v_h__2_16_, v_val_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(v_x_23_, v_h__1_24_, v_h__2_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_){
_start:
{
switch(lean_obj_tag(v_x_27_))
{
case 0:
{
lean_object* v_it_31_; lean_object* v_out_32_; lean_object* v___x_33_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v_it_31_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_it_31_);
v_out_32_ = lean_ctor_get(v_x_27_, 1);
lean_inc(v_out_32_);
lean_dec_ref(v_x_27_);
v___x_33_ = lean_apply_2(v_h__1_28_, v_it_31_, v_out_32_);
return v___x_33_;
}
case 1:
{
lean_object* v_it_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__1_28_);
v_it_34_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_it_34_);
lean_dec_ref(v_x_27_);
v___x_35_ = lean_apply_1(v_h__2_29_, v_it_34_);
return v___x_35_;
}
default: 
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_29_);
lean_dec(v_h__1_28_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__3_30_, v___x_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_motive_40_, lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_41_, v_h__1_42_, v_h__2_43_, v_h__3_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(lean_object* v_____do__lift_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_____do__lift_46_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_47_);
v_a_49_ = lean_ctor_get(v_____do__lift_46_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_____do__lift_46_);
v___x_50_ = lean_apply_1(v_h__2_48_, v_a_49_);
return v___x_50_;
}
else
{
lean_object* v_a_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_48_);
v_a_51_ = lean_ctor_get(v_____do__lift_46_, 0);
lean_inc(v_a_51_);
lean_dec_ref(v_____do__lift_46_);
v___x_52_ = lean_apply_1(v_h__1_47_, v_a_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(lean_object* v_00_u03b3_53_, lean_object* v_motive_54_, lean_object* v_____do__lift_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(v_____do__lift_55_, v_h__1_56_, v_h__2_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
lean_object* v_it_63_; lean_object* v_out_64_; lean_object* v___x_65_; 
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
v_it_63_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_it_63_);
v_out_64_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_out_64_);
lean_dec_ref(v_x_59_);
v___x_65_ = lean_apply_3(v_h__1_60_, v_it_63_, v_out_64_, lean_box(0));
return v___x_65_;
}
case 1:
{
lean_object* v_it_66_; lean_object* v___x_67_; 
lean_dec(v_h__3_62_);
lean_dec(v_h__1_60_);
v_it_66_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_it_66_);
lean_dec_ref(v_x_59_);
v___x_67_ = lean_apply_2(v_h__2_61_, v_it_66_, lean_box(0));
return v___x_67_;
}
default: 
{
lean_object* v___x_68_; 
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v___x_68_ = lean_apply_1(v_h__3_62_, lean_box(0));
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_inst_71_, lean_object* v_it_72_, lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_74_, v_h__1_75_, v_h__2_76_, v_h__3_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_inst_81_, lean_object* v_it_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_79_, v_00_u03b2_80_, v_inst_81_, v_it_82_, v_motive_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_it_82_);
lean_dec(v_inst_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_____do__lift_89_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v_a_92_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v_____do__lift_89_);
v___x_93_ = lean_apply_1(v_h__2_91_, v_a_92_);
return v___x_93_;
}
else
{
lean_object* v_a_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v_a_94_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_a_94_);
lean_dec_ref(v_____do__lift_89_);
v___x_95_ = lean_apply_1(v_h__1_90_, v_a_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_96_, lean_object* v_motive_97_, lean_object* v_____do__lift_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_98_, v_h__1_99_, v_h__2_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v___x_105_; 
lean_dec(v_h__2_104_);
v___x_105_ = lean_apply_1(v_h__1_103_, lean_box(0));
return v___x_105_;
}
else
{
lean_object* v_val_106_; lean_object* v___x_107_; 
lean_dec(v_h__1_103_);
v_val_106_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_val_106_);
lean_dec_ref(v_x_102_);
v___x_107_ = lean_apply_2(v_h__2_104_, v_val_106_, lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(lean_object* v_00_u03b1_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(v_x_110_, v_h__1_111_, v_h__2_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
lean_dec(v_h__2_116_);
v_a_117_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v_x_114_);
v___x_118_ = lean_apply_1(v_h__1_115_, v_a_117_);
return v___x_118_;
}
else
{
lean_object* v_a_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_115_);
v_a_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v_x_114_);
v___x_120_ = lean_apply_1(v_h__2_116_, v_a_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_121_, lean_object* v_motive_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_123_, v_h__1_124_, v_h__2_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_129_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__1_128_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_128_);
v_val_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_val_132_);
lean_dec_ref(v_x_127_);
v___x_133_ = lean_apply_1(v_h__2_129_, v_val_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(lean_object* v_00_u03b1_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(v_x_136_, v_h__1_137_, v_h__2_138_);
return v___x_139_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
