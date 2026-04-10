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
lean_dec_ref(v_x_10_);
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
uint8_t v_x_26__boxed_27_; lean_object* v_res_28_; 
v_x_26__boxed_27_ = lean_unbox(v_x_24_);
v_res_28_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_27_, v_h__1_25_, v_h__2_26_);
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
uint8_t v_x_37__boxed_41_; lean_object* v_res_42_; 
v_x_37__boxed_41_ = lean_unbox(v_x_38_);
v_res_42_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(v_motive_37_, v_x_37__boxed_41_, v_h__1_39_, v_h__2_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_, lean_object* v_h__3_48_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_dec(v_h__2_47_);
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_49_; 
lean_dec(v_h__3_48_);
v___x_49_ = lean_apply_1(v_h__1_46_, v_x_45_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v_h__1_46_);
v___x_50_ = lean_apply_5(v_h__3_48_, v_x_43_, v_x_44_, v_x_45_, lean_box(0), lean_box(0));
return v___x_50_;
}
}
else
{
lean_dec(v_h__1_46_);
if (lean_obj_tag(v_x_44_) == 1)
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_48_);
v_head_51_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_head_51_);
v_tail_52_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_tail_52_);
lean_dec_ref(v_x_43_);
v_head_53_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_54_);
lean_dec_ref(v_x_44_);
v___x_55_ = lean_apply_5(v_h__2_47_, v_head_51_, v_tail_52_, v_head_53_, v_tail_54_, v_x_45_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; 
lean_dec(v_h__2_47_);
v___x_56_ = lean_apply_5(v_h__3_48_, v_x_43_, v_x_44_, v_x_45_, lean_box(0), lean_box(0));
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_57_, lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_dec(v_h__2_63_);
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_65_; 
lean_dec(v_h__3_64_);
v___x_65_ = lean_apply_1(v_h__1_62_, v_x_61_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_dec(v_h__1_62_);
v___x_66_ = lean_apply_5(v_h__3_64_, v_x_59_, v_x_60_, v_x_61_, lean_box(0), lean_box(0));
return v___x_66_;
}
}
else
{
lean_dec(v_h__1_62_);
if (lean_obj_tag(v_x_60_) == 1)
{
lean_object* v_head_67_; lean_object* v_tail_68_; lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v___x_71_; 
lean_dec(v_h__3_64_);
v_head_67_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_head_67_);
v_tail_68_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_tail_68_);
lean_dec_ref(v_x_59_);
v_head_69_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_70_);
lean_dec_ref(v_x_60_);
v___x_71_ = lean_apply_5(v_h__2_63_, v_head_67_, v_tail_68_, v_head_69_, v_tail_70_, v_x_61_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; 
lean_dec(v_h__2_63_);
v___x_72_ = lean_apply_5(v_h__3_64_, v_x_59_, v_x_60_, v_x_61_, lean_box(0), lean_box(0));
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_77_; 
lean_dec(v_h__3_76_);
lean_dec(v_h__2_75_);
v___x_77_ = lean_apply_1(v_h__1_74_, lean_box(0));
return v___x_77_;
}
else
{
lean_object* v_tail_78_; 
lean_dec(v_h__1_74_);
v_tail_78_ = lean_ctor_get(v_x_73_, 1);
if (lean_obj_tag(v_tail_78_) == 0)
{
lean_object* v_head_79_; lean_object* v___x_80_; 
lean_dec(v_h__3_76_);
v_head_79_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_head_79_);
lean_dec_ref(v_x_73_);
v___x_80_ = lean_apply_2(v_h__2_75_, v_head_79_, lean_box(0));
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_84_; 
lean_inc_ref(v_tail_78_);
lean_dec(v_h__2_75_);
v_head_81_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_head_81_);
lean_dec_ref(v_x_73_);
v_head_82_ = lean_ctor_get(v_tail_78_, 0);
lean_inc(v_head_82_);
v_tail_83_ = lean_ctor_get(v_tail_78_, 1);
lean_inc(v_tail_83_);
lean_dec_ref(v_tail_78_);
v___x_84_ = lean_apply_4(v_h__3_76_, v_head_81_, v_head_82_, v_tail_83_, lean_box(0));
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(lean_object* v_00_u03b1_85_, lean_object* v_motive_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_, lean_object* v_h__3_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_92_; 
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
v___x_92_ = lean_apply_1(v_h__1_89_, lean_box(0));
return v___x_92_;
}
else
{
lean_object* v_tail_93_; 
lean_dec(v_h__1_89_);
v_tail_93_ = lean_ctor_get(v_x_87_, 1);
if (lean_obj_tag(v_tail_93_) == 0)
{
lean_object* v_head_94_; lean_object* v___x_95_; 
lean_dec(v_h__3_91_);
v_head_94_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_94_);
lean_dec_ref(v_x_87_);
v___x_95_ = lean_apply_2(v_h__2_90_, v_head_94_, lean_box(0));
return v___x_95_;
}
else
{
lean_object* v_head_96_; lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_99_; 
lean_inc_ref(v_tail_93_);
lean_dec(v_h__2_90_);
v_head_96_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_96_);
lean_dec_ref(v_x_87_);
v_head_97_ = lean_ctor_get(v_tail_93_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_tail_93_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_tail_93_);
v___x_99_ = lean_apply_4(v_h__3_91_, v_head_96_, v_head_97_, v_tail_98_, lean_box(0));
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_102_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__1_101_, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_107_; 
lean_dec(v_h__1_101_);
v_head_105_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_head_105_);
v_tail_106_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_tail_106_);
lean_dec_ref(v_x_100_);
v___x_107_ = lean_apply_2(v_h__2_102_, v_head_105_, v_tail_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(lean_object* v_00_u03b1_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_112_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__1_111_, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v___x_117_; 
lean_dec(v_h__1_111_);
v_head_115_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_head_115_);
v_tail_116_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_tail_116_);
lean_dec_ref(v_x_110_);
v___x_117_ = lean_apply_2(v_h__2_112_, v_head_115_, v_tail_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__2_120_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__1_119_, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_head_123_; lean_object* v_tail_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_119_);
v_head_123_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_head_123_);
v_tail_124_ = lean_ctor_get(v_x_118_, 1);
lean_inc(v_tail_124_);
lean_dec_ref(v_x_118_);
v___x_125_ = lean_apply_2(v_h__2_120_, v_head_123_, v_tail_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_126_, lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_130_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__1_129_, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_129_);
v_head_133_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_133_);
v_tail_134_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_134_);
lean_dec_ref(v_x_128_);
v___x_135_ = lean_apply_2(v_h__2_130_, v_head_133_, v_tail_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_140_; 
lean_dec(v_h__2_139_);
v___x_140_ = lean_apply_1(v_h__1_138_, v_x_137_);
return v___x_140_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_138_);
v_head_141_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_head_141_);
v_tail_142_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_tail_142_);
lean_dec_ref(v_x_136_);
v___x_143_ = lean_apply_3(v_h__2_139_, v_head_141_, v_tail_142_, v_x_137_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_144_, lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_150_; 
lean_dec(v_h__2_149_);
v___x_150_ = lean_apply_1(v_h__1_148_, v_x_147_);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v___x_153_; 
lean_dec(v_h__1_148_);
v_head_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_tail_152_);
lean_dec_ref(v_x_146_);
v___x_153_ = lean_apply_3(v_h__2_149_, v_head_151_, v_tail_152_, v_x_147_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__2_156_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__1_155_, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
lean_dec(v_h__1_155_);
v_val_159_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v_x_154_);
v___x_160_ = lean_apply_1(v_h__2_156_, v_val_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_161_, lean_object* v_motive_162_, lean_object* v_x_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_165_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__1_164_, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_164_);
v_val_168_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v_x_163_);
v___x_169_ = lean_apply_1(v_h__2_165_, v_val_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
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
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v___x_177_; 
lean_dec(v_h__1_171_);
v_head_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_head_175_);
v_tail_176_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_tail_176_);
lean_dec_ref(v_x_170_);
v___x_177_ = lean_apply_2(v_h__2_172_, v_head_175_, v_tail_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(lean_object* v_00_u03b1_178_, lean_object* v_motive_179_, lean_object* v_x_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_182_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__1_181_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_181_);
v_head_185_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_185_);
v_tail_186_ = lean_ctor_get(v_x_180_, 1);
lean_inc(v_tail_186_);
lean_dec_ref(v_x_180_);
v___x_187_ = lean_apply_2(v_h__2_182_, v_head_185_, v_tail_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__1_189_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__2_190_, v___x_191_);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
lean_dec(v_h__2_190_);
v_val_193_ = lean_ctor_get(v_x_188_, 0);
lean_inc(v_val_193_);
lean_dec_ref(v_x_188_);
v___x_194_ = lean_apply_1(v_h__1_189_, v_val_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_195_, lean_object* v_motive_196_, lean_object* v_x_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_h__1_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_1(v_h__2_199_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; 
lean_dec(v_h__2_199_);
v_val_202_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v_x_197_);
v___x_203_ = lean_apply_1(v_h__1_198_, v_val_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_){
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
lean_dec_ref(v_x_204_);
v___x_210_ = lean_apply_1(v_h__2_206_, v_val_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_211_, lean_object* v_motive_212_, lean_object* v_x_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
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
lean_dec_ref(v_x_213_);
v___x_219_ = lean_apply_1(v_h__2_215_, v_val_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
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
lean_dec_ref(v_x_220_);
v___x_226_ = lean_apply_1(v_h__1_221_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_227_, lean_object* v_motive_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
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
lean_dec_ref(v_x_229_);
v___x_235_ = lean_apply_1(v_h__1_230_, v_val_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object* v_x_236_, lean_object* v_y_237_, lean_object* v_hy_238_, lean_object* v_x_239_, lean_object* v_hx_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_4(v_x_236_, v_y_237_, v_hy_238_, v_x_239_, lean_box(0));
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_dec(v_x_246_);
lean_dec(v_x_244_);
lean_dec(v_x_243_);
return v_x_245_;
}
else
{
lean_object* v_head_247_; lean_object* v_tail_248_; lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_head_247_ = lean_ctor_get(v_x_242_, 0);
lean_inc_n(v_head_247_, 2);
v_tail_248_ = lean_ctor_get(v_x_242_, 1);
lean_inc(v_tail_248_);
lean_dec_ref(v_x_242_);
lean_inc(v_x_246_);
v___f_249_ = lean_alloc_closure((void*)(l_List_foldlRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_249_, 0, v_x_246_);
lean_inc(v_x_243_);
lean_inc(v_x_244_);
v___x_250_ = lean_apply_2(v_x_243_, v_x_244_, v_head_247_);
v___x_251_ = lean_apply_4(v_x_246_, v_x_244_, v_x_245_, v_head_247_, lean_box(0));
v_x_242_ = v_tail_248_;
v_x_244_ = v___x_250_;
v_x_245_ = v___x_251_;
v_x_246_ = v___f_249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object* v_00_u03b2_253_, lean_object* v_00_u03b1_254_, lean_object* v_motive_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_List_foldlRecOn___redArg(v_x_256_, v_x_257_, v_x_258_, v_x_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___lam__0(lean_object* v_x_262_, lean_object* v_b_263_, lean_object* v_c_264_, lean_object* v_a_265_, lean_object* v_m_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_apply_4(v_x_262_, v_b_263_, v_c_264_, v_a_265_, lean_box(0));
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(lean_object* v_x_268_, lean_object* v_init_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_dec(v_x_268_);
lean_inc(v_init_269_);
return v_init_269_;
}
else
{
lean_object* v_head_271_; lean_object* v_tail_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_head_271_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_head_271_);
v_tail_272_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_tail_272_);
lean_dec_ref(v_x_270_);
lean_inc(v_x_268_);
v___x_273_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_268_, v_init_269_, v_tail_272_);
v___x_274_ = lean_apply_2(v_x_268_, v_head_271_, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(lean_object* v_x_275_, lean_object* v_init_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_275_, v_init_276_, v_x_277_);
lean_dec(v_init_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg(lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_dec(v_x_283_);
lean_dec(v_x_280_);
lean_inc(v_x_282_);
return v_x_282_;
}
else
{
lean_object* v_head_284_; lean_object* v_tail_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_head_284_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_head_284_);
v_tail_285_ = lean_ctor_get(v_x_279_, 1);
lean_inc_n(v_tail_285_, 2);
lean_dec_ref(v_x_279_);
lean_inc(v_x_283_);
v___f_286_ = lean_alloc_closure((void*)(l_List_foldrRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_286_, 0, v_x_283_);
lean_inc(v_x_280_);
v___x_287_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_280_, v_x_281_, v_tail_285_);
v___x_288_ = l_List_foldrRecOn___redArg(v_tail_285_, v_x_280_, v_x_281_, v_x_282_, v___f_286_);
v___x_289_ = lean_apply_4(v_x_283_, v___x_287_, v___x_288_, v_head_284_, lean_box(0));
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_List_foldrRecOn___redArg(v_x_290_, v_x_291_, v_x_292_, v_x_293_, v_x_294_);
lean_dec(v_x_293_);
lean_dec(v_x_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn(lean_object* v_00_u03b2_296_, lean_object* v_00_u03b1_297_, lean_object* v_motive_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_List_foldrRecOn___redArg(v_x_299_, v_x_300_, v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___boxed(lean_object* v_00_u03b2_305_, lean_object* v_00_u03b1_306_, lean_object* v_motive_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_List_foldrRecOn(v_00_u03b2_305_, v_00_u03b1_306_, v_motive_307_, v_x_308_, v_x_309_, v_x_310_, v_x_311_, v_x_312_);
lean_dec(v_x_311_);
lean_dec(v_x_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_x_316_, lean_object* v_init_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_316_, v_init_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_x_322_, lean_object* v_init_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_List_foldr___at___00List_foldrRecOn_spec__0(v_00_u03b1_320_, v_00_u03b2_321_, v_x_322_, v_init_323_, v_x_324_);
lean_dec(v_init_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_332_; 
lean_dec(v_h__2_329_);
v_fst_330_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v_x_327_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v_x_327_);
v___x_332_ = lean_apply_2(v_h__1_328_, v_fst_330_, v_snd_331_);
return v___x_332_;
}
else
{
lean_object* v_head_333_; lean_object* v_tail_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_337_; 
lean_dec(v_h__1_328_);
v_head_333_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_head_333_);
v_tail_334_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_tail_334_);
lean_dec_ref(v_x_326_);
v_fst_335_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_x_327_, 1);
lean_inc(v_snd_336_);
lean_dec_ref(v_x_327_);
v___x_337_ = lean_apply_4(v_h__2_329_, v_head_333_, v_tail_334_, v_fst_335_, v_snd_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(lean_object* v_00_u03b1_338_, lean_object* v_motive_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_346_; 
lean_dec(v_h__2_343_);
v_fst_344_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_snd_345_);
lean_dec_ref(v_x_341_);
v___x_346_ = lean_apply_2(v_h__1_342_, v_fst_344_, v_snd_345_);
return v___x_346_;
}
else
{
lean_object* v_head_347_; lean_object* v_tail_348_; lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_342_);
v_head_347_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_head_347_);
v_tail_348_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_tail_348_);
lean_dec_ref(v_x_340_);
v_fst_349_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_fst_349_);
v_snd_350_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_snd_350_);
lean_dec_ref(v_x_341_);
v___x_351_ = lean_apply_4(v_h__2_343_, v_head_347_, v_tail_348_, v_fst_349_, v_snd_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_, lean_object* v_h__3_357_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
lean_object* v___x_358_; 
lean_dec(v_h__3_357_);
lean_dec(v_h__2_356_);
v___x_358_ = lean_apply_2(v_h__1_355_, v_x_353_, v_x_354_);
return v___x_358_;
}
else
{
lean_object* v_head_359_; lean_object* v_tail_360_; lean_object* v_zero_361_; uint8_t v_isZero_362_; 
lean_dec(v_h__1_355_);
v_head_359_ = lean_ctor_get(v_x_352_, 0);
v_tail_360_ = lean_ctor_get(v_x_352_, 1);
v_zero_361_ = lean_unsigned_to_nat(0u);
v_isZero_362_ = lean_nat_dec_eq(v_x_353_, v_zero_361_);
if (v_isZero_362_ == 0)
{
lean_object* v_one_363_; lean_object* v_n_364_; lean_object* v___x_365_; 
lean_inc(v_tail_360_);
lean_inc(v_head_359_);
lean_dec_ref(v_x_352_);
lean_dec(v_h__3_357_);
v_one_363_ = lean_unsigned_to_nat(1u);
v_n_364_ = lean_nat_sub(v_x_353_, v_one_363_);
lean_dec(v_x_353_);
v___x_365_ = lean_apply_4(v_h__2_356_, v_head_359_, v_tail_360_, v_n_364_, v_x_354_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_h__2_356_);
v___x_366_ = lean_apply_5(v_h__3_357_, v_x_352_, v_x_353_, v_x_354_, lean_box(0), lean_box(0));
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object* v_00_u03b1_367_, lean_object* v_motive_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_, lean_object* v_h__3_374_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v___x_375_; 
lean_dec(v_h__3_374_);
lean_dec(v_h__2_373_);
v___x_375_ = lean_apply_2(v_h__1_372_, v_x_370_, v_x_371_);
return v___x_375_;
}
else
{
lean_object* v_head_376_; lean_object* v_tail_377_; lean_object* v_zero_378_; uint8_t v_isZero_379_; 
lean_dec(v_h__1_372_);
v_head_376_ = lean_ctor_get(v_x_369_, 0);
v_tail_377_ = lean_ctor_get(v_x_369_, 1);
v_zero_378_ = lean_unsigned_to_nat(0u);
v_isZero_379_ = lean_nat_dec_eq(v_x_370_, v_zero_378_);
if (v_isZero_379_ == 0)
{
lean_object* v_one_380_; lean_object* v_n_381_; lean_object* v___x_382_; 
lean_inc(v_tail_377_);
lean_inc(v_head_376_);
lean_dec_ref(v_x_369_);
lean_dec(v_h__3_374_);
v_one_380_ = lean_unsigned_to_nat(1u);
v_n_381_ = lean_nat_sub(v_x_370_, v_one_380_);
lean_dec(v_x_370_);
v___x_382_ = lean_apply_4(v_h__2_373_, v_head_376_, v_tail_377_, v_n_381_, v_x_371_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; 
lean_dec(v_h__2_373_);
v___x_383_ = lean_apply_5(v_h__3_374_, v_x_369_, v_x_370_, v_x_371_, lean_box(0), lean_box(0));
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_388_; 
lean_dec(v_h__2_387_);
v___x_388_ = lean_apply_1(v_h__1_386_, v_x_385_);
return v___x_388_;
}
else
{
lean_object* v_head_389_; lean_object* v_tail_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_386_);
v_head_389_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_389_);
v_tail_390_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_tail_390_);
lean_dec_ref(v_x_384_);
v___x_391_ = lean_apply_3(v_h__2_387_, v_head_389_, v_tail_390_, v_x_385_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_392_, lean_object* v_motive_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_398_; 
lean_dec(v_h__2_397_);
v___x_398_ = lean_apply_1(v_h__1_396_, v_x_395_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; 
lean_dec(v_h__1_396_);
v_head_399_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_head_399_);
v_tail_400_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_tail_400_);
lean_dec_ref(v_x_394_);
v___x_401_ = lean_apply_3(v_h__2_397_, v_head_399_, v_tail_400_, v_x_395_);
return v___x_401_;
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
