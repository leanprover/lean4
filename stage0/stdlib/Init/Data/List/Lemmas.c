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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_43_, 2);
v_head_53_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_54_);
lean_dec_ref_known(v_x_44_, 2);
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
lean_dec_ref_known(v_x_59_, 2);
v_head_69_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_60_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_h__2_75_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_apply_1(v_h__1_74_, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v_val_78_; lean_object* v___x_79_; 
lean_dec(v_h__1_74_);
v_val_78_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_x_73_, 1);
v___x_79_ = lean_apply_1(v_h__2_75_, v_val_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_80_, lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_h__2_84_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_1(v_h__1_83_, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_83_);
v_val_87_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v_x_82_, 1);
v___x_88_ = lean_apply_1(v_h__2_84_, v_val_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__2_91_, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v_val_94_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v_x_89_, 1);
v___x_95_ = lean_apply_1(v_h__1_90_, v_val_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_96_, lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__2_100_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_100_);
v_val_103_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v_x_98_, 1);
v___x_104_ = lean_apply_1(v_h__1_99_, v_val_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__2_107_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__1_106_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_111_; 
lean_dec(v_h__1_106_);
v_val_110_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_110_);
lean_dec_ref_known(v_x_105_, 1);
v___x_111_ = lean_apply_1(v_h__2_107_, v_val_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_112_, lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__2_116_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__1_115_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_115_);
v_val_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v_x_114_, 1);
v___x_120_ = lean_apply_1(v_h__2_116_, v_val_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_122_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_apply_1(v_h__2_123_, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v___x_127_; 
lean_dec(v_h__2_123_);
v_val_126_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v_x_121_, 1);
v___x_127_ = lean_apply_1(v_h__1_122_, v_val_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_131_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__2_132_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_132_);
v_val_135_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_x_130_, 1);
v___x_136_ = lean_apply_1(v_h__1_131_, v_val_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object* v_x_137_, lean_object* v_y_138_, lean_object* v_hy_139_, lean_object* v_x_140_, lean_object* v_hx_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_4(v_x_137_, v_y_138_, v_hy_139_, v_x_140_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_dec(v_x_147_);
lean_dec(v_x_145_);
lean_dec(v_x_144_);
return v_x_146_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_head_148_ = lean_ctor_get(v_x_143_, 0);
lean_inc_n(v_head_148_, 2);
v_tail_149_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_tail_149_);
lean_dec_ref_known(v_x_143_, 2);
lean_inc(v_x_147_);
v___f_150_ = lean_alloc_closure((void*)(l_List_foldlRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_150_, 0, v_x_147_);
lean_inc(v_x_144_);
lean_inc(v_x_145_);
v___x_151_ = lean_apply_2(v_x_144_, v_x_145_, v_head_148_);
v___x_152_ = lean_apply_4(v_x_147_, v_x_145_, v_x_146_, v_head_148_, lean_box(0));
v_x_143_ = v_tail_149_;
v_x_145_ = v___x_151_;
v_x_146_ = v___x_152_;
v_x_147_ = v___f_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object* v_00_u03b2_154_, lean_object* v_00_u03b1_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_List_foldlRecOn___redArg(v_x_157_, v_x_158_, v_x_159_, v_x_160_, v_x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___lam__0(lean_object* v_x_163_, lean_object* v_b_164_, lean_object* v_c_165_, lean_object* v_a_166_, lean_object* v_m_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_apply_4(v_x_163_, v_b_164_, v_c_165_, v_a_166_, lean_box(0));
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(lean_object* v_x_169_, lean_object* v_init_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_dec(v_x_169_);
lean_inc(v_init_170_);
return v_init_170_;
}
else
{
lean_object* v_head_172_; lean_object* v_tail_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_head_172_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_head_172_);
v_tail_173_ = lean_ctor_get(v_x_171_, 1);
lean_inc(v_tail_173_);
lean_dec_ref_known(v_x_171_, 2);
lean_inc(v_x_169_);
v___x_174_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_169_, v_init_170_, v_tail_173_);
v___x_175_ = lean_apply_2(v_x_169_, v_head_172_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(lean_object* v_x_176_, lean_object* v_init_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_176_, v_init_177_, v_x_178_);
lean_dec(v_init_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_dec(v_x_184_);
lean_dec(v_x_181_);
lean_inc(v_x_183_);
return v_x_183_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_head_185_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_185_);
v_tail_186_ = lean_ctor_get(v_x_180_, 1);
lean_inc_n(v_tail_186_, 2);
lean_dec_ref_known(v_x_180_, 2);
lean_inc(v_x_184_);
v___f_187_ = lean_alloc_closure((void*)(l_List_foldrRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_187_, 0, v_x_184_);
lean_inc(v_x_181_);
v___x_188_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_181_, v_x_182_, v_tail_186_);
v___x_189_ = l_List_foldrRecOn___redArg(v_tail_186_, v_x_181_, v_x_182_, v_x_183_, v___f_187_);
v___x_190_ = lean_apply_4(v_x_184_, v___x_188_, v___x_189_, v_head_185_, lean_box(0));
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___boxed(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_List_foldrRecOn___redArg(v_x_191_, v_x_192_, v_x_193_, v_x_194_, v_x_195_);
lean_dec(v_x_194_);
lean_dec(v_x_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn(lean_object* v_00_u03b2_197_, lean_object* v_00_u03b1_198_, lean_object* v_motive_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_List_foldrRecOn___redArg(v_x_200_, v_x_201_, v_x_202_, v_x_203_, v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___boxed(lean_object* v_00_u03b2_206_, lean_object* v_00_u03b1_207_, lean_object* v_motive_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_List_foldrRecOn(v_00_u03b2_206_, v_00_u03b1_207_, v_motive_208_, v_x_209_, v_x_210_, v_x_211_, v_x_212_, v_x_213_);
lean_dec(v_x_212_);
lean_dec(v_x_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_x_217_, lean_object* v_init_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_217_, v_init_218_, v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_x_223_, lean_object* v_init_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_List_foldr___at___00List_foldrRecOn_spec__0(v_00_u03b1_221_, v_00_u03b2_222_, v_x_223_, v_init_224_, v_x_225_);
lean_dec(v_init_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_, lean_object* v_h__3_232_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_233_; 
lean_dec(v_h__3_232_);
lean_dec(v_h__2_231_);
v___x_233_ = lean_apply_2(v_h__1_230_, v_x_228_, v_x_229_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_tail_235_; lean_object* v_zero_236_; uint8_t v_isZero_237_; 
lean_dec(v_h__1_230_);
v_head_234_ = lean_ctor_get(v_x_227_, 0);
v_tail_235_ = lean_ctor_get(v_x_227_, 1);
v_zero_236_ = lean_unsigned_to_nat(0u);
v_isZero_237_ = lean_nat_dec_eq(v_x_228_, v_zero_236_);
if (v_isZero_237_ == 0)
{
lean_object* v_one_238_; lean_object* v_n_239_; lean_object* v___x_240_; 
lean_inc(v_tail_235_);
lean_inc(v_head_234_);
lean_dec_ref_known(v_x_227_, 2);
lean_dec(v_h__3_232_);
v_one_238_ = lean_unsigned_to_nat(1u);
v_n_239_ = lean_nat_sub(v_x_228_, v_one_238_);
lean_dec(v_x_228_);
v___x_240_ = lean_apply_4(v_h__2_231_, v_head_234_, v_tail_235_, v_n_239_, v_x_229_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v_h__2_231_);
v___x_241_ = lean_apply_5(v_h__3_232_, v_x_227_, v_x_228_, v_x_229_, lean_box(0), lean_box(0));
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object* v_00_u03b1_242_, lean_object* v_motive_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_, lean_object* v_h__3_249_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v___x_250_; 
lean_dec(v_h__3_249_);
lean_dec(v_h__2_248_);
v___x_250_ = lean_apply_2(v_h__1_247_, v_x_245_, v_x_246_);
return v___x_250_;
}
else
{
lean_object* v_head_251_; lean_object* v_tail_252_; lean_object* v_zero_253_; uint8_t v_isZero_254_; 
lean_dec(v_h__1_247_);
v_head_251_ = lean_ctor_get(v_x_244_, 0);
v_tail_252_ = lean_ctor_get(v_x_244_, 1);
v_zero_253_ = lean_unsigned_to_nat(0u);
v_isZero_254_ = lean_nat_dec_eq(v_x_245_, v_zero_253_);
if (v_isZero_254_ == 0)
{
lean_object* v_one_255_; lean_object* v_n_256_; lean_object* v___x_257_; 
lean_inc(v_tail_252_);
lean_inc(v_head_251_);
lean_dec_ref_known(v_x_244_, 2);
lean_dec(v_h__3_249_);
v_one_255_ = lean_unsigned_to_nat(1u);
v_n_256_ = lean_nat_sub(v_x_245_, v_one_255_);
lean_dec(v_x_245_);
v___x_257_ = lean_apply_4(v_h__2_248_, v_head_251_, v_tail_252_, v_n_256_, v_x_246_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v_h__2_248_);
v___x_258_ = lean_apply_5(v_h__3_249_, v_x_244_, v_x_245_, v_x_246_, lean_box(0), lean_box(0));
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v___x_263_; 
lean_dec(v_h__2_262_);
v___x_263_ = lean_apply_1(v_h__1_261_, v_x_260_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v___x_266_; 
lean_dec(v_h__1_261_);
v_head_264_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_head_264_);
v_tail_265_ = lean_ctor_get(v_x_259_, 1);
lean_inc(v_tail_265_);
lean_dec_ref_known(v_x_259_, 2);
v___x_266_ = lean_apply_3(v_h__2_262_, v_head_264_, v_tail_265_, v_x_260_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_267_, lean_object* v_motive_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v___x_273_; 
lean_dec(v_h__2_272_);
v___x_273_ = lean_apply_1(v_h__1_271_, v_x_270_);
return v___x_273_;
}
else
{
lean_object* v_head_274_; lean_object* v_tail_275_; lean_object* v___x_276_; 
lean_dec(v_h__1_271_);
v_head_274_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_head_274_);
v_tail_275_ = lean_ctor_get(v_x_269_, 1);
lean_inc(v_tail_275_);
lean_dec_ref_known(v_x_269_, 2);
v___x_276_ = lean_apply_3(v_h__2_272_, v_head_274_, v_tail_275_, v_x_270_);
return v___x_276_;
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
