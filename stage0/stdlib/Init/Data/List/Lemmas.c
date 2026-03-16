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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (v_x_14_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_15_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
uint8_t v_x_22__boxed_24_; lean_object* v_res_25_; 
v_x_22__boxed_24_ = lean_unbox(v_x_21_);
v_res_25_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_24_, v_h__1_22_, v_h__2_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_26_, uint8_t v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_27_, v_h__1_28_, v_h__2_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
uint8_t v_x_33__boxed_35_; lean_object* v_res_36_; 
v_x_33__boxed_35_ = lean_unbox(v_x_32_);
v_res_36_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(v_motive_31_, v_x_33__boxed_35_, v_h__1_33_, v_h__2_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_x_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_dec(v_h__2_41_);
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v___x_43_; 
lean_dec(v_h__3_42_);
v___x_43_ = lean_apply_1(v_h__1_40_, v_x_39_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; 
lean_dec(v_h__1_40_);
v___x_44_ = lean_apply_5(v_h__3_42_, v_x_37_, v_x_38_, v_x_39_, lean_box(0), lean_box(0));
return v___x_44_;
}
}
else
{
lean_dec(v_h__1_40_);
if (lean_obj_tag(v_x_38_) == 1)
{
lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_42_);
v_head_45_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_head_45_);
v_tail_46_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_tail_46_);
lean_dec_ref(v_x_37_);
v_head_47_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_tail_48_);
lean_dec_ref(v_x_38_);
v___x_49_ = lean_apply_5(v_h__2_41_, v_head_45_, v_tail_46_, v_head_47_, v_tail_48_, v_x_39_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v_h__2_41_);
v___x_50_ = lean_apply_5(v_h__3_42_, v_x_37_, v_x_38_, v_x_39_, lean_box(0), lean_box(0));
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_dec(v_h__2_57_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_59_; 
lean_dec(v_h__3_58_);
v___x_59_ = lean_apply_1(v_h__1_56_, v_x_55_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
lean_dec(v_h__1_56_);
v___x_60_ = lean_apply_5(v_h__3_58_, v_x_53_, v_x_54_, v_x_55_, lean_box(0), lean_box(0));
return v___x_60_;
}
}
else
{
lean_dec(v_h__1_56_);
if (lean_obj_tag(v_x_54_) == 1)
{
lean_object* v_head_61_; lean_object* v_tail_62_; lean_object* v_head_63_; lean_object* v_tail_64_; lean_object* v___x_65_; 
lean_dec(v_h__3_58_);
v_head_61_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_61_);
v_tail_62_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_62_);
lean_dec_ref(v_x_53_);
v_head_63_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_63_);
v_tail_64_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_64_);
lean_dec_ref(v_x_54_);
v___x_65_ = lean_apply_5(v_h__2_57_, v_head_61_, v_tail_62_, v_head_63_, v_tail_64_, v_x_55_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_dec(v_h__2_57_);
v___x_66_ = lean_apply_5(v_h__3_58_, v_x_53_, v_x_54_, v_x_55_, lean_box(0), lean_box(0));
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_71_; 
lean_dec(v_h__3_70_);
lean_dec(v_h__2_69_);
v___x_71_ = lean_apply_1(v_h__1_68_, lean_box(0));
return v___x_71_;
}
else
{
lean_object* v_tail_72_; 
lean_dec(v_h__1_68_);
v_tail_72_ = lean_ctor_get(v_x_67_, 1);
if (lean_obj_tag(v_tail_72_) == 0)
{
lean_object* v_head_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_70_);
v_head_73_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_head_73_);
lean_dec_ref(v_x_67_);
v___x_74_ = lean_apply_2(v_h__2_69_, v_head_73_, lean_box(0));
return v___x_74_;
}
else
{
lean_object* v_head_75_; lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
lean_inc_ref(v_tail_72_);
lean_dec(v_h__2_69_);
v_head_75_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_head_75_);
lean_dec_ref(v_x_67_);
v_head_76_ = lean_ctor_get(v_tail_72_, 0);
lean_inc(v_head_76_);
v_tail_77_ = lean_ctor_get(v_tail_72_, 1);
lean_inc(v_tail_77_);
lean_dec_ref(v_tail_72_);
v___x_78_ = lean_apply_4(v_h__3_70_, v_head_75_, v_head_76_, v_tail_77_, lean_box(0));
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(lean_object* v_00_u03b1_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_, lean_object* v_h__3_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(v_x_81_, v_h__1_83_, v_h__2_84_, v_h__3_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(lean_object* v_x_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_89_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__1_88_, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_88_);
v_head_92_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_93_);
lean_dec_ref(v_x_87_);
v___x_94_ = lean_apply_2(v_h__2_89_, v_head_92_, v_tail_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(lean_object* v_00_u03b1_95_, lean_object* v_motive_96_, lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(v_x_97_, v_h__1_98_, v_h__2_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_103_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__1_102_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v___x_108_; 
lean_dec(v_h__1_102_);
v_head_106_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_tail_107_);
lean_dec_ref(v_x_101_);
v___x_108_ = lean_apply_2(v_h__2_103_, v_head_106_, v_tail_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_109_, lean_object* v_motive_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(v_x_111_, v_h__1_112_, v_h__2_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_119_; 
lean_dec(v_h__2_118_);
v___x_119_ = lean_apply_1(v_h__1_117_, v_x_116_);
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_117_);
v_head_120_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_head_120_);
v_tail_121_ = lean_ctor_get(v_x_115_, 1);
lean_inc(v_tail_121_);
lean_dec_ref(v_x_115_);
v___x_122_ = lean_apply_3(v_h__2_118_, v_head_120_, v_tail_121_, v_x_116_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_123_, lean_object* v_motive_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(v_x_125_, v_x_126_, v_h__1_127_, v_h__2_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__2_132_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__1_131_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_131_);
v_val_135_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v_x_130_);
v___x_136_ = lean_apply_1(v_h__2_132_, v_val_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_137_, lean_object* v_motive_138_, lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(v_x_139_, v_h__1_140_, v_h__2_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_145_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_apply_1(v_h__1_144_, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_144_);
v_head_148_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_head_148_);
v_tail_149_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_tail_149_);
lean_dec_ref(v_x_143_);
v___x_150_ = lean_apply_2(v_h__2_145_, v_head_148_, v_tail_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(lean_object* v_00_u03b1_151_, lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(v_x_153_, v_h__1_154_, v_h__2_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_158_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__2_159_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_163_; 
lean_dec(v_h__2_159_);
v_val_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_val_162_);
lean_dec_ref(v_x_157_);
v___x_163_ = lean_apply_1(v_h__1_158_, v_val_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_164_, lean_object* v_motive_165_, lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(v_x_166_, v_h__1_167_, v_h__2_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_172_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_h__1_171_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; 
lean_dec(v_h__1_171_);
v_val_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_val_175_);
lean_dec_ref(v_x_170_);
v___x_176_ = lean_apply_1(v_h__2_172_, v_val_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_177_, lean_object* v_motive_178_, lean_object* v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(v_x_179_, v_h__1_180_, v_h__2_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_1(v_h__2_185_, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v_val_188_; lean_object* v___x_189_; 
lean_dec(v_h__2_185_);
v_val_188_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_val_188_);
lean_dec_ref(v_x_183_);
v___x_189_ = lean_apply_1(v_h__1_184_, v_val_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_190_, lean_object* v_motive_191_, lean_object* v_x_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(v_x_192_, v_h__1_193_, v_h__2_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object* v_x_196_, lean_object* v_y_197_, lean_object* v_hy_198_, lean_object* v_x_199_, lean_object* v_hx_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_apply_4(v_x_196_, v_y_197_, v_hy_198_, v_x_199_, lean_box(0));
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_dec(v_x_206_);
lean_dec(v_x_204_);
lean_dec(v_x_203_);
return v_x_205_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_head_207_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_head_207_);
v_tail_208_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_tail_208_);
lean_dec_ref(v_x_202_);
lean_inc(v_x_206_);
v___f_209_ = lean_alloc_closure((void*)(l_List_foldlRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_209_, 0, v_x_206_);
lean_inc(v_x_203_);
lean_inc(v_head_207_);
lean_inc(v_x_204_);
v___x_210_ = lean_apply_2(v_x_203_, v_x_204_, v_head_207_);
v___x_211_ = lean_apply_4(v_x_206_, v_x_204_, v_x_205_, v_head_207_, lean_box(0));
v_x_202_ = v_tail_208_;
v_x_204_ = v___x_210_;
v_x_205_ = v___x_211_;
v_x_206_ = v___f_209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object* v_00_u03b2_213_, lean_object* v_00_u03b1_214_, lean_object* v_motive_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_List_foldlRecOn___redArg(v_x_216_, v_x_217_, v_x_218_, v_x_219_, v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___lam__0(lean_object* v_x_222_, lean_object* v_b_223_, lean_object* v_c_224_, lean_object* v_a_225_, lean_object* v_m_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_apply_4(v_x_222_, v_b_223_, v_c_224_, v_a_225_, lean_box(0));
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(lean_object* v_x_228_, lean_object* v_init_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_dec(v_x_228_);
lean_inc(v_init_229_);
return v_init_229_;
}
else
{
lean_object* v_head_231_; lean_object* v_tail_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_head_231_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_head_231_);
v_tail_232_ = lean_ctor_get(v_x_230_, 1);
lean_inc(v_tail_232_);
lean_dec_ref(v_x_230_);
lean_inc(v_x_228_);
v___x_233_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_228_, v_init_229_, v_tail_232_);
v___x_234_ = lean_apply_2(v_x_228_, v_head_231_, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(lean_object* v_x_235_, lean_object* v_init_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_235_, v_init_236_, v_x_237_);
lean_dec(v_init_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_dec(v_x_243_);
lean_dec(v_x_240_);
lean_inc(v_x_242_);
return v_x_242_;
}
else
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_head_244_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_head_244_);
v_tail_245_ = lean_ctor_get(v_x_239_, 1);
lean_inc(v_tail_245_);
lean_dec_ref(v_x_239_);
lean_inc(v_x_243_);
v___f_246_ = lean_alloc_closure((void*)(l_List_foldrRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_246_, 0, v_x_243_);
lean_inc(v_tail_245_);
lean_inc(v_x_240_);
v___x_247_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_240_, v_x_241_, v_tail_245_);
v___x_248_ = l_List_foldrRecOn___redArg(v_tail_245_, v_x_240_, v_x_241_, v_x_242_, v___f_246_);
v___x_249_ = lean_apply_4(v_x_243_, v___x_247_, v___x_248_, v_head_244_, lean_box(0));
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___boxed(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_List_foldrRecOn___redArg(v_x_250_, v_x_251_, v_x_252_, v_x_253_, v_x_254_);
lean_dec(v_x_253_);
lean_dec(v_x_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn(lean_object* v_00_u03b2_256_, lean_object* v_00_u03b1_257_, lean_object* v_motive_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_List_foldrRecOn___redArg(v_x_259_, v_x_260_, v_x_261_, v_x_262_, v_x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___boxed(lean_object* v_00_u03b2_265_, lean_object* v_00_u03b1_266_, lean_object* v_motive_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_List_foldrRecOn(v_00_u03b2_265_, v_00_u03b1_266_, v_motive_267_, v_x_268_, v_x_269_, v_x_270_, v_x_271_, v_x_272_);
lean_dec(v_x_271_);
lean_dec(v_x_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_x_276_, lean_object* v_init_277_, lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_276_, v_init_277_, v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_x_282_, lean_object* v_init_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_List_foldr___at___00List_foldrRecOn_spec__0(v_00_u03b1_280_, v_00_u03b2_281_, v_x_282_, v_init_283_, v_x_284_);
lean_dec(v_init_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v_fst_290_; lean_object* v_snd_291_; lean_object* v___x_292_; 
lean_dec(v_h__2_289_);
v_fst_290_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_fst_290_);
v_snd_291_ = lean_ctor_get(v_x_287_, 1);
lean_inc(v_snd_291_);
lean_dec_ref(v_x_287_);
v___x_292_ = lean_apply_2(v_h__1_288_, v_fst_290_, v_snd_291_);
return v___x_292_;
}
else
{
lean_object* v_head_293_; lean_object* v_tail_294_; lean_object* v_fst_295_; lean_object* v_snd_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_288_);
v_head_293_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_head_293_);
v_tail_294_ = lean_ctor_get(v_x_286_, 1);
lean_inc(v_tail_294_);
lean_dec_ref(v_x_286_);
v_fst_295_ = lean_ctor_get(v_x_287_, 0);
lean_inc(v_fst_295_);
v_snd_296_ = lean_ctor_get(v_x_287_, 1);
lean_inc(v_snd_296_);
lean_dec_ref(v_x_287_);
v___x_297_ = lean_apply_4(v_h__2_289_, v_head_293_, v_tail_294_, v_fst_295_, v_snd_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(lean_object* v_00_u03b1_298_, lean_object* v_motive_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(v_x_300_, v_x_301_, v_h__1_302_, v_h__2_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_, lean_object* v_h__3_310_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_311_; 
lean_dec(v_h__3_310_);
lean_dec(v_h__2_309_);
v___x_311_ = lean_apply_2(v_h__1_308_, v_x_306_, v_x_307_);
return v___x_311_;
}
else
{
lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v_zero_314_; uint8_t v_isZero_315_; 
lean_dec(v_h__1_308_);
v_head_312_ = lean_ctor_get(v_x_305_, 0);
v_tail_313_ = lean_ctor_get(v_x_305_, 1);
v_zero_314_ = lean_unsigned_to_nat(0u);
v_isZero_315_ = lean_nat_dec_eq(v_x_306_, v_zero_314_);
if (v_isZero_315_ == 0)
{
lean_object* v_one_316_; lean_object* v_n_317_; lean_object* v___x_318_; 
lean_inc(v_tail_313_);
lean_inc(v_head_312_);
lean_dec_ref(v_x_305_);
lean_dec(v_h__3_310_);
v_one_316_ = lean_unsigned_to_nat(1u);
v_n_317_ = lean_nat_sub(v_x_306_, v_one_316_);
lean_dec(v_x_306_);
v___x_318_ = lean_apply_4(v_h__2_309_, v_head_312_, v_tail_313_, v_n_317_, v_x_307_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
lean_dec(v_h__2_309_);
v___x_319_ = lean_apply_5(v_h__3_310_, v_x_305_, v_x_306_, v_x_307_, lean_box(0), lean_box(0));
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object* v_00_u03b1_320_, lean_object* v_motive_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_, lean_object* v_h__3_327_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v___x_328_; 
lean_dec(v_h__3_327_);
lean_dec(v_h__2_326_);
v___x_328_ = lean_apply_2(v_h__1_325_, v_x_323_, v_x_324_);
return v___x_328_;
}
else
{
lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v_zero_331_; uint8_t v_isZero_332_; 
lean_dec(v_h__1_325_);
v_head_329_ = lean_ctor_get(v_x_322_, 0);
v_tail_330_ = lean_ctor_get(v_x_322_, 1);
v_zero_331_ = lean_unsigned_to_nat(0u);
v_isZero_332_ = lean_nat_dec_eq(v_x_323_, v_zero_331_);
if (v_isZero_332_ == 0)
{
lean_object* v_one_333_; lean_object* v_n_334_; lean_object* v___x_335_; 
lean_inc(v_tail_330_);
lean_inc(v_head_329_);
lean_dec_ref(v_x_322_);
lean_dec(v_h__3_327_);
v_one_333_ = lean_unsigned_to_nat(1u);
v_n_334_ = lean_nat_sub(v_x_323_, v_one_333_);
lean_dec(v_x_323_);
v___x_335_ = lean_apply_4(v_h__2_326_, v_head_329_, v_tail_330_, v_n_334_, v_x_324_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
lean_dec(v_h__2_326_);
v___x_336_ = lean_apply_5(v_h__3_327_, v_x_322_, v_x_323_, v_x_324_, lean_box(0), lean_box(0));
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_341_; 
lean_dec(v_h__2_340_);
v___x_341_ = lean_apply_1(v_h__1_339_, v_x_338_);
return v___x_341_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_339_);
v_head_342_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_head_342_);
v_tail_343_ = lean_ctor_get(v_x_337_, 1);
lean_inc(v_tail_343_);
lean_dec_ref(v_x_337_);
v___x_344_ = lean_apply_3(v_h__2_340_, v_head_342_, v_tail_343_, v_x_338_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_345_, lean_object* v_motive_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(v_x_347_, v_x_348_, v_h__1_349_, v_h__2_350_);
return v___x_351_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
