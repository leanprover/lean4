// Lean compiler output
// Module: Init.Data.List.Lemmas
// Imports: public import Init.Data.List.BasicAux import all Init.Data.List.BasicAux public import Init.Data.List.Control import all Init.Data.List.Control public import Init.BinderPredicates import Init.Grind.Annotated public import Init.Data.BEq public import Init.Data.Option.Instances import Init.Data.Bool import Init.Data.Option.Lemmas import Init.TacticsExtra
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_set_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_set_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (v_x_17_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_h__1_18_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_apply_1(v_h__2_19_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_19_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_18_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
uint8_t v_x_24__boxed_27_; lean_object* v_res_28_; 
v_x_24__boxed_27_ = lean_unbox(v_x_24_);
v_res_28_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_27_, v_h__1_25_, v_h__2_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_29_, uint8_t v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (v_x_30_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_31_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__2_32_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_32_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_31_, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
uint8_t v_x_35__boxed_41_; lean_object* v_res_42_; 
v_x_35__boxed_41_ = lean_unbox(v_x_38_);
v_res_42_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(v_motive_37_, v_x_35__boxed_41_, v_h__1_39_, v_h__2_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_set_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_, lean_object* v_h__3_48_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
lean_dec(v_h__1_46_);
v___x_49_ = lean_apply_2(v_h__3_48_, v_x_44_, v_x_45_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v_zero_52_; uint8_t v_isZero_53_; 
lean_dec(v_h__3_48_);
v_head_50_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_head_50_);
v_tail_51_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_tail_51_);
lean_dec_ref_known(v_x_43_, 2);
v_zero_52_ = lean_unsigned_to_nat(0u);
v_isZero_53_ = lean_nat_dec_eq(v_x_44_, v_zero_52_);
if (v_isZero_53_ == 1)
{
lean_object* v___x_54_; 
lean_dec(v_h__2_47_);
lean_dec(v_x_44_);
v___x_54_ = lean_apply_3(v_h__1_46_, v_head_50_, v_tail_51_, v_x_45_);
return v___x_54_;
}
else
{
lean_object* v_one_55_; lean_object* v_n_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_46_);
v_one_55_ = lean_unsigned_to_nat(1u);
v_n_56_ = lean_nat_sub(v_x_44_, v_one_55_);
lean_dec(v_x_44_);
v___x_57_ = lean_apply_4(v_h__2_47_, v_head_50_, v_tail_51_, v_n_56_, v_x_45_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_set_match__1_splitter(lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_, lean_object* v_h__3_65_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_66_; 
lean_dec(v_h__2_64_);
lean_dec(v_h__1_63_);
v___x_66_ = lean_apply_2(v_h__3_65_, v_x_61_, v_x_62_);
return v___x_66_;
}
else
{
lean_object* v_head_67_; lean_object* v_tail_68_; lean_object* v_zero_69_; uint8_t v_isZero_70_; 
lean_dec(v_h__3_65_);
v_head_67_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_67_);
v_tail_68_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_68_);
lean_dec_ref_known(v_x_60_, 2);
v_zero_69_ = lean_unsigned_to_nat(0u);
v_isZero_70_ = lean_nat_dec_eq(v_x_61_, v_zero_69_);
if (v_isZero_70_ == 1)
{
lean_object* v___x_71_; 
lean_dec(v_h__2_64_);
lean_dec(v_x_61_);
v___x_71_ = lean_apply_3(v_h__1_63_, v_head_67_, v_tail_68_, v_x_62_);
return v___x_71_;
}
else
{
lean_object* v_one_72_; lean_object* v_n_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_63_);
v_one_72_ = lean_unsigned_to_nat(1u);
v_n_73_ = lean_nat_sub(v_x_61_, v_one_72_);
lean_dec(v_x_61_);
v___x_74_ = lean_apply_4(v_h__2_64_, v_head_67_, v_tail_68_, v_n_73_, v_x_62_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_, lean_object* v_h__3_80_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_dec(v_h__2_79_);
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_81_; 
lean_dec(v_h__3_80_);
v___x_81_ = lean_apply_1(v_h__1_78_, v_x_77_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
lean_dec(v_h__1_78_);
v___x_82_ = lean_apply_5(v_h__3_80_, v_x_75_, v_x_76_, v_x_77_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
else
{
lean_dec(v_h__1_78_);
if (lean_obj_tag(v_x_76_) == 1)
{
lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v_head_85_; lean_object* v_tail_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_80_);
v_head_83_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_head_83_);
v_tail_84_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_tail_84_);
lean_dec_ref_known(v_x_75_, 2);
v_head_85_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_head_85_);
v_tail_86_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_tail_86_);
lean_dec_ref_known(v_x_76_, 2);
v___x_87_ = lean_apply_5(v_h__2_79_, v_head_83_, v_tail_84_, v_head_85_, v_tail_86_, v_x_77_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v_h__2_79_);
v___x_88_ = lean_apply_5(v_h__3_80_, v_x_75_, v_x_76_, v_x_77_, lean_box(0), lean_box(0));
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_89_, lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_dec(v_h__2_95_);
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_97_; 
lean_dec(v_h__3_96_);
v___x_97_ = lean_apply_1(v_h__1_94_, v_x_93_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_h__1_94_);
v___x_98_ = lean_apply_5(v_h__3_96_, v_x_91_, v_x_92_, v_x_93_, lean_box(0), lean_box(0));
return v___x_98_;
}
}
else
{
lean_dec(v_h__1_94_);
if (lean_obj_tag(v_x_92_) == 1)
{
lean_object* v_head_99_; lean_object* v_tail_100_; lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_103_; 
lean_dec(v_h__3_96_);
v_head_99_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_99_);
v_tail_100_ = lean_ctor_get(v_x_91_, 1);
lean_inc(v_tail_100_);
lean_dec_ref_known(v_x_91_, 2);
v_head_101_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_head_101_);
v_tail_102_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_tail_102_);
lean_dec_ref_known(v_x_92_, 2);
v___x_103_ = lean_apply_5(v_h__2_95_, v_head_99_, v_tail_100_, v_head_101_, v_tail_102_, v_x_93_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v_h__2_95_);
v___x_104_ = lean_apply_5(v_h__3_96_, v_x_91_, v_x_92_, v_x_93_, lean_box(0), lean_box(0));
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_109_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v___x_109_ = lean_apply_1(v_h__1_106_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v_tail_110_; 
lean_dec(v_h__1_106_);
v_tail_110_ = lean_ctor_get(v_x_105_, 1);
if (lean_obj_tag(v_tail_110_) == 0)
{
lean_object* v_head_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_108_);
v_head_111_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_head_111_);
lean_dec_ref_known(v_x_105_, 2);
v___x_112_ = lean_apply_2(v_h__2_107_, v_head_111_, lean_box(0));
return v___x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v___x_116_; 
lean_inc_ref(v_tail_110_);
lean_dec(v_h__2_107_);
v_head_113_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_head_113_);
lean_dec_ref_known(v_x_105_, 2);
v_head_114_ = lean_ctor_get(v_tail_110_, 0);
lean_inc(v_head_114_);
v_tail_115_ = lean_ctor_get(v_tail_110_, 1);
lean_inc(v_tail_115_);
lean_dec_ref_known(v_tail_110_, 2);
v___x_116_ = lean_apply_4(v_h__3_108_, v_head_113_, v_head_114_, v_tail_115_, lean_box(0));
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(lean_object* v_00_u03b1_117_, lean_object* v_motive_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_, lean_object* v_h__3_123_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_124_; 
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
v___x_124_ = lean_apply_1(v_h__1_121_, lean_box(0));
return v___x_124_;
}
else
{
lean_object* v_tail_125_; 
lean_dec(v_h__1_121_);
v_tail_125_ = lean_ctor_get(v_x_119_, 1);
if (lean_obj_tag(v_tail_125_) == 0)
{
lean_object* v_head_126_; lean_object* v___x_127_; 
lean_dec(v_h__3_123_);
v_head_126_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_head_126_);
lean_dec_ref_known(v_x_119_, 2);
v___x_127_ = lean_apply_2(v_h__2_122_, v_head_126_, lean_box(0));
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_131_; 
lean_inc_ref(v_tail_125_);
lean_dec(v_h__2_122_);
v_head_128_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_head_128_);
lean_dec_ref_known(v_x_119_, 2);
v_head_129_ = lean_ctor_get(v_tail_125_, 0);
lean_inc(v_head_129_);
v_tail_130_ = lean_ctor_get(v_tail_125_, 1);
lean_inc(v_tail_130_);
lean_dec_ref_known(v_tail_125_, 2);
v___x_131_ = lean_apply_4(v_h__3_123_, v_head_128_, v_head_129_, v_tail_130_, lean_box(0));
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_134_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__1_133_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_133_);
v_head_137_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_head_137_);
v_tail_138_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_tail_138_);
lean_dec_ref_known(v_x_132_, 2);
v___x_139_ = lean_apply_2(v_h__2_134_, v_head_137_, v_tail_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(lean_object* v_00_u03b1_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_144_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__1_143_, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v_head_147_; lean_object* v_tail_148_; lean_object* v___x_149_; 
lean_dec(v_h__1_143_);
v_head_147_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_147_);
v_tail_148_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_tail_148_);
lean_dec_ref_known(v_x_142_, 2);
v___x_149_ = lean_apply_2(v_h__2_144_, v_head_147_, v_tail_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__2_152_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_1(v_h__1_151_, v___x_153_);
return v___x_154_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; lean_object* v___x_157_; 
lean_dec(v_h__1_151_);
v_head_155_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_head_155_);
v_tail_156_ = lean_ctor_get(v_x_150_, 1);
lean_inc(v_tail_156_);
lean_dec_ref_known(v_x_150_, 2);
v___x_157_ = lean_apply_2(v_h__2_152_, v_head_155_, v_tail_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_158_, lean_object* v_motive_159_, lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_162_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_1(v_h__1_161_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_161_);
v_head_165_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_head_165_);
v_tail_166_ = lean_ctor_get(v_x_160_, 1);
lean_inc(v_tail_166_);
lean_dec_ref_known(v_x_160_, 2);
v___x_167_ = lean_apply_2(v_h__2_162_, v_head_165_, v_tail_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v___x_172_; 
lean_dec(v_h__2_171_);
v___x_172_ = lean_apply_1(v_h__1_170_, v_x_169_);
return v___x_172_;
}
else
{
lean_object* v_head_173_; lean_object* v_tail_174_; lean_object* v___x_175_; 
lean_dec(v_h__1_170_);
v_head_173_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_head_173_);
v_tail_174_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_tail_174_);
lean_dec_ref_known(v_x_168_, 2);
v___x_175_ = lean_apply_3(v_h__2_171_, v_head_173_, v_tail_174_, v_x_169_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_176_, lean_object* v_motive_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_182_; 
lean_dec(v_h__2_181_);
v___x_182_ = lean_apply_1(v_h__1_180_, v_x_179_);
return v___x_182_;
}
else
{
lean_object* v_head_183_; lean_object* v_tail_184_; lean_object* v___x_185_; 
lean_dec(v_h__1_180_);
v_head_183_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_head_183_);
v_tail_184_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_tail_184_);
lean_dec_ref_known(v_x_178_, 2);
v___x_185_ = lean_apply_3(v_h__2_181_, v_head_183_, v_tail_184_, v_x_179_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
if (lean_obj_tag(v_ys_186_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_h__2_188_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_apply_1(v_h__1_187_, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_head_191_; lean_object* v_tail_192_; lean_object* v___x_193_; 
lean_dec(v_h__1_187_);
v_head_191_ = lean_ctor_get(v_ys_186_, 0);
lean_inc(v_head_191_);
v_tail_192_ = lean_ctor_get(v_ys_186_, 1);
lean_inc(v_tail_192_);
lean_dec_ref_known(v_ys_186_, 2);
v___x_193_ = lean_apply_2(v_h__2_188_, v_head_191_, v_tail_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_194_, lean_object* v_motive_195_, lean_object* v_ys_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
if (lean_obj_tag(v_ys_196_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__2_198_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__1_197_, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_197_);
v_head_201_ = lean_ctor_get(v_ys_196_, 0);
lean_inc(v_head_201_);
v_tail_202_ = lean_ctor_get(v_ys_196_, 1);
lean_inc(v_tail_202_);
lean_dec_ref_known(v_ys_196_, 2);
v___x_203_ = lean_apply_2(v_h__2_198_, v_head_201_, v_tail_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__2_206_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_h__1_205_, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_210_; 
lean_dec(v_h__1_205_);
v_val_209_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v_x_204_, 1);
v___x_210_ = lean_apply_1(v_h__2_206_, v_val_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_211_, lean_object* v_motive_212_, lean_object* v_x_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_h__2_215_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v_h__1_214_, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
lean_dec(v_h__1_214_);
v_val_218_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_x_213_, 1);
v___x_219_ = lean_apply_1(v_h__2_215_, v_val_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__1_221_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__2_222_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_dec(v_h__2_222_);
v_val_225_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_x_220_, 1);
v___x_226_ = lean_apply_1(v_h__1_221_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_227_, lean_object* v_motive_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_h__2_231_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_235_; 
lean_dec(v_h__2_231_);
v_val_234_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v_x_229_, 1);
v___x_235_ = lean_apply_1(v_h__1_230_, v_val_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v_h__2_238_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_apply_1(v_h__1_237_, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v___x_243_; 
lean_dec(v_h__1_237_);
v_head_241_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_head_241_);
v_tail_242_ = lean_ctor_get(v_x_236_, 1);
lean_inc(v_tail_242_);
lean_dec_ref_known(v_x_236_, 2);
v___x_243_ = lean_apply_2(v_h__2_238_, v_head_241_, v_tail_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(lean_object* v_00_u03b1_244_, lean_object* v_motive_245_, lean_object* v_x_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_h__2_248_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_apply_1(v_h__1_247_, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v_head_251_; lean_object* v_tail_252_; lean_object* v___x_253_; 
lean_dec(v_h__1_247_);
v_head_251_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_head_251_);
v_tail_252_ = lean_ctor_get(v_x_246_, 1);
lean_inc(v_tail_252_);
lean_dec_ref_known(v_x_246_, 2);
v___x_253_ = lean_apply_2(v_h__2_248_, v_head_251_, v_tail_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_254_, lean_object* v_h__1_255_, lean_object* v_h__2_256_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_255_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_1(v_h__2_256_, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_256_);
v_val_259_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v_x_254_, 1);
v___x_260_ = lean_apply_1(v_h__1_255_, v_val_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_261_, lean_object* v_motive_262_, lean_object* v_x_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_h__1_264_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_apply_1(v_h__2_265_, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v_val_268_; lean_object* v___x_269_; 
lean_dec(v_h__2_265_);
v_val_268_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_val_268_);
lean_dec_ref_known(v_x_263_, 1);
v___x_269_ = lean_apply_1(v_h__1_264_, v_val_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_h__1_272_, lean_object* v_h__2_273_){
_start:
{
lean_object* v_zero_274_; uint8_t v_isZero_275_; 
v_zero_274_ = lean_unsigned_to_nat(0u);
v_isZero_275_ = lean_nat_dec_eq(v_x_270_, v_zero_274_);
if (v_isZero_275_ == 1)
{
lean_object* v___x_276_; 
lean_dec(v_h__2_273_);
v___x_276_ = lean_apply_1(v_h__1_272_, v_x_271_);
return v___x_276_;
}
else
{
lean_object* v_one_277_; lean_object* v_n_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_272_);
v_one_277_ = lean_unsigned_to_nat(1u);
v_n_278_ = lean_nat_sub(v_x_270_, v_one_277_);
v___x_279_ = lean_apply_2(v_h__2_273_, v_n_278_, v_x_271_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___redArg(v_x_280_, v_x_281_, v_h__1_282_, v_h__2_283_);
lean_dec(v_x_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_285_, lean_object* v_motive_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_h__1_289_, lean_object* v_h__2_290_){
_start:
{
lean_object* v_zero_291_; uint8_t v_isZero_292_; 
v_zero_291_ = lean_unsigned_to_nat(0u);
v_isZero_292_ = lean_nat_dec_eq(v_x_287_, v_zero_291_);
if (v_isZero_292_ == 1)
{
lean_object* v___x_293_; 
lean_dec(v_h__2_290_);
v___x_293_ = lean_apply_1(v_h__1_289_, v_x_288_);
return v___x_293_;
}
else
{
lean_object* v_one_294_; lean_object* v_n_295_; lean_object* v___x_296_; 
lean_dec(v_h__1_289_);
v_one_294_ = lean_unsigned_to_nat(1u);
v_n_295_ = lean_nat_sub(v_x_287_, v_one_294_);
v___x_296_ = lean_apply_2(v_h__2_290_, v_n_295_, v_x_288_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_297_, lean_object* v_motive_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_h__1_301_, lean_object* v_h__2_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Init_Data_List_Lemmas_0__List_replicate_match__1_splitter(v_00_u03b1_297_, v_motive_298_, v_x_299_, v_x_300_, v_h__1_301_, v_h__2_302_);
lean_dec(v_x_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_h__2_306_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__1_305_, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_310_; 
lean_dec(v_h__1_305_);
v_val_309_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v_x_304_, 1);
v___x_310_ = lean_apply_1(v_h__2_306_, v_val_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_311_, lean_object* v_motive_312_, lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__2_315_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__1_314_, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; 
lean_dec(v_h__1_314_);
v_val_318_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_x_313_, 1);
v___x_319_ = lean_apply_1(v_h__2_315_, v_val_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_object* v___x_324_; 
lean_dec(v_h__2_323_);
v___x_324_ = lean_apply_1(v_h__1_322_, v_x_321_);
return v___x_324_;
}
else
{
lean_object* v_head_325_; lean_object* v_tail_326_; lean_object* v___x_327_; 
lean_dec(v_h__1_322_);
v_head_325_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_head_325_);
v_tail_326_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_tail_326_);
lean_dec_ref_known(v_x_320_, 2);
v___x_327_ = lean_apply_3(v_h__2_323_, v_head_325_, v_tail_326_, v_x_321_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_328_, lean_object* v_motive_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
lean_object* v___x_334_; 
lean_dec(v_h__2_333_);
v___x_334_ = lean_apply_1(v_h__1_332_, v_x_331_);
return v___x_334_;
}
else
{
lean_object* v_head_335_; lean_object* v_tail_336_; lean_object* v___x_337_; 
lean_dec(v_h__1_332_);
v_head_335_ = lean_ctor_get(v_x_330_, 0);
lean_inc(v_head_335_);
v_tail_336_ = lean_ctor_get(v_x_330_, 1);
lean_inc(v_tail_336_);
lean_dec_ref_known(v_x_330_, 2);
v___x_337_ = lean_apply_3(v_h__2_333_, v_head_335_, v_tail_336_, v_x_331_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v_h__1_339_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_apply_1(v_h__2_340_, v___x_341_);
return v___x_342_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_344_; 
lean_dec(v_h__2_340_);
v_val_343_ = lean_ctor_get(v_x_338_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_x_338_, 1);
v___x_344_ = lean_apply_1(v_h__1_339_, v_val_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_345_, lean_object* v_motive_346_, lean_object* v_x_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_348_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__2_349_, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_353_; 
lean_dec(v_h__2_349_);
v_val_352_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v_x_347_, 1);
v___x_353_ = lean_apply_1(v_h__1_348_, v_val_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object* v_x_354_, lean_object* v_y_355_, lean_object* v_hy_356_, lean_object* v_x_357_, lean_object* v_hx_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_4(v_x_354_, v_y_355_, v_hy_356_, v_x_357_, lean_box(0));
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_dec(v_x_364_);
lean_dec(v_x_362_);
lean_dec(v_x_361_);
return v_x_363_;
}
else
{
lean_object* v_head_365_; lean_object* v_tail_366_; lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_head_365_ = lean_ctor_get(v_x_360_, 0);
lean_inc_n(v_head_365_, 2);
v_tail_366_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_tail_366_);
lean_dec_ref_known(v_x_360_, 2);
lean_inc(v_x_364_);
v___f_367_ = lean_alloc_closure((void*)(l_List_foldlRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_367_, 0, v_x_364_);
lean_inc(v_x_361_);
lean_inc(v_x_362_);
v___x_368_ = lean_apply_2(v_x_361_, v_x_362_, v_head_365_);
v___x_369_ = lean_apply_4(v_x_364_, v_x_362_, v_x_363_, v_head_365_, lean_box(0));
v_x_360_ = v_tail_366_;
v_x_362_ = v___x_368_;
v_x_363_ = v___x_369_;
v_x_364_ = v___f_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object* v_00_u03b2_371_, lean_object* v_00_u03b1_372_, lean_object* v_motive_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_List_foldlRecOn___redArg(v_x_374_, v_x_375_, v_x_376_, v_x_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_386_; 
lean_dec(v_h__2_383_);
v_fst_384_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v_x_381_, 1);
lean_inc(v_snd_385_);
lean_dec_ref(v_x_381_);
v___x_386_ = lean_apply_2(v_h__1_382_, v_fst_384_, v_snd_385_);
return v___x_386_;
}
else
{
lean_object* v_head_387_; lean_object* v_tail_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_382_);
v_head_387_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_head_387_);
v_tail_388_ = lean_ctor_get(v_x_380_, 1);
lean_inc(v_tail_388_);
lean_dec_ref_known(v_x_380_, 2);
v_fst_389_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_x_381_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v_x_381_);
v___x_391_ = lean_apply_4(v_h__2_383_, v_head_387_, v_tail_388_, v_fst_389_, v_snd_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(lean_object* v_00_u03b1_392_, lean_object* v_motive_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v_fst_398_; lean_object* v_snd_399_; lean_object* v___x_400_; 
lean_dec(v_h__2_397_);
v_fst_398_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_fst_398_);
v_snd_399_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_snd_399_);
lean_dec_ref(v_x_395_);
v___x_400_ = lean_apply_2(v_h__1_396_, v_fst_398_, v_snd_399_);
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_405_; 
lean_dec(v_h__1_396_);
v_head_401_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_head_401_);
v_tail_402_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_tail_402_);
lean_dec_ref_known(v_x_394_, 2);
v_fst_403_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v_x_395_);
v___x_405_ = lean_apply_4(v_h__2_397_, v_head_401_, v_tail_402_, v_fst_403_, v_snd_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_, lean_object* v_h__3_409_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_h__3_409_);
lean_dec(v_h__2_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_1(v_h__1_407_, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_tail_412_; 
lean_dec(v_h__1_407_);
v_tail_412_ = lean_ctor_get(v_x_406_, 1);
if (lean_obj_tag(v_tail_412_) == 0)
{
lean_object* v_head_413_; lean_object* v___x_414_; 
lean_dec(v_h__3_409_);
v_head_413_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_head_413_);
lean_dec_ref_known(v_x_406_, 2);
v___x_414_ = lean_apply_1(v_h__2_408_, v_head_413_);
return v___x_414_;
}
else
{
lean_object* v_head_415_; lean_object* v___x_416_; 
lean_inc(v_tail_412_);
lean_dec(v_h__2_408_);
v_head_415_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_head_415_);
lean_dec_ref_known(v_x_406_, 2);
v___x_416_ = lean_apply_3(v_h__3_409_, v_head_415_, v_tail_412_, lean_box(0));
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_417_, lean_object* v_motive_418_, lean_object* v_x_419_, lean_object* v_h__1_420_, lean_object* v_h__2_421_, lean_object* v_h__3_422_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_h__3_422_);
lean_dec(v_h__2_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_1(v_h__1_420_, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v_tail_425_; 
lean_dec(v_h__1_420_);
v_tail_425_ = lean_ctor_get(v_x_419_, 1);
if (lean_obj_tag(v_tail_425_) == 0)
{
lean_object* v_head_426_; lean_object* v___x_427_; 
lean_dec(v_h__3_422_);
v_head_426_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_head_426_);
lean_dec_ref_known(v_x_419_, 2);
v___x_427_ = lean_apply_1(v_h__2_421_, v_head_426_);
return v___x_427_;
}
else
{
lean_object* v_head_428_; lean_object* v___x_429_; 
lean_inc(v_tail_425_);
lean_dec(v_h__2_421_);
v_head_428_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_head_428_);
lean_dec_ref_known(v_x_419_, 2);
v___x_429_ = lean_apply_3(v_h__3_422_, v_head_428_, v_tail_425_, lean_box(0));
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_h__1_433_, lean_object* v_h__2_434_, lean_object* v_h__3_435_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_436_; 
lean_dec(v_h__3_435_);
lean_dec(v_h__2_434_);
v___x_436_ = lean_apply_2(v_h__1_433_, v_x_431_, v_x_432_);
return v___x_436_;
}
else
{
lean_object* v_head_437_; lean_object* v_tail_438_; lean_object* v_zero_439_; uint8_t v_isZero_440_; 
lean_dec(v_h__1_433_);
v_head_437_ = lean_ctor_get(v_x_430_, 0);
v_tail_438_ = lean_ctor_get(v_x_430_, 1);
v_zero_439_ = lean_unsigned_to_nat(0u);
v_isZero_440_ = lean_nat_dec_eq(v_x_431_, v_zero_439_);
if (v_isZero_440_ == 0)
{
lean_object* v_one_441_; lean_object* v_n_442_; lean_object* v___x_443_; 
lean_inc(v_tail_438_);
lean_inc(v_head_437_);
lean_dec_ref_known(v_x_430_, 2);
lean_dec(v_h__3_435_);
v_one_441_ = lean_unsigned_to_nat(1u);
v_n_442_ = lean_nat_sub(v_x_431_, v_one_441_);
lean_dec(v_x_431_);
v___x_443_ = lean_apply_4(v_h__2_434_, v_head_437_, v_tail_438_, v_n_442_, v_x_432_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v_h__2_434_);
v___x_444_ = lean_apply_5(v_h__3_435_, v_x_430_, v_x_431_, v_x_432_, lean_box(0), lean_box(0));
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object* v_00_u03b1_445_, lean_object* v_motive_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_, lean_object* v_h__3_452_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_453_; 
lean_dec(v_h__3_452_);
lean_dec(v_h__2_451_);
v___x_453_ = lean_apply_2(v_h__1_450_, v_x_448_, v_x_449_);
return v___x_453_;
}
else
{
lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v_zero_456_; uint8_t v_isZero_457_; 
lean_dec(v_h__1_450_);
v_head_454_ = lean_ctor_get(v_x_447_, 0);
v_tail_455_ = lean_ctor_get(v_x_447_, 1);
v_zero_456_ = lean_unsigned_to_nat(0u);
v_isZero_457_ = lean_nat_dec_eq(v_x_448_, v_zero_456_);
if (v_isZero_457_ == 0)
{
lean_object* v_one_458_; lean_object* v_n_459_; lean_object* v___x_460_; 
lean_inc(v_tail_455_);
lean_inc(v_head_454_);
lean_dec_ref_known(v_x_447_, 2);
lean_dec(v_h__3_452_);
v_one_458_ = lean_unsigned_to_nat(1u);
v_n_459_ = lean_nat_sub(v_x_448_, v_one_458_);
lean_dec(v_x_448_);
v___x_460_ = lean_apply_4(v_h__2_451_, v_head_454_, v_tail_455_, v_n_459_, v_x_449_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_h__2_451_);
v___x_461_ = lean_apply_5(v_h__3_452_, v_x_447_, v_x_448_, v_x_449_, lean_box(0), lean_box(0));
return v___x_461_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Annotated(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Grind_Annotated(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
