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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
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
LEAN_EXPORT void l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_17_ = stack[0].m_num;
lean_object* v_h__1_18_ = stack[1].m_obj;
lean_object* v_h__2_19_ = stack[2].m_obj;
lean_object* v_res_24_;
v_res_24_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
uint8_t v_x_24__boxed_28_; lean_object* v_res_29_; 
v_x_24__boxed_28_ = lean_unbox(v_x_25_);
v_res_29_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_28_, v_h__1_26_, v_h__2_27_);
return v_res_29_;
}
}
lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(lean_object* v_motive_30_, uint8_t v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (v_x_31_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_32_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__2_33_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_33_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__1_32_, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_31_ = stack[1].m_num;
lean_object* v_h__1_32_ = stack[2].m_obj;
lean_object* v_h__2_33_ = stack[3].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(lean_box(0), v_x_31_, v_h__1_32_, v_h__2_33_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
uint8_t v_x_41__boxed_43_; lean_object* v_res_44_; 
v_x_41__boxed_43_ = lean_unbox(v_x_40_);
v_res_44_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(v_motive_39_, v_x_41__boxed_43_, v_h__1_41_, v_h__2_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_dec(v_h__2_49_);
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_51_; 
lean_dec(v_h__3_50_);
v___x_51_ = lean_apply_1(v_h__1_48_, v_x_47_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
lean_dec(v_h__1_48_);
v___x_52_ = lean_apply_5(v_h__3_50_, v_x_45_, v_x_46_, v_x_47_, lean_box(0), lean_box(0));
return v___x_52_;
}
}
else
{
lean_dec(v_h__1_48_);
if (lean_obj_tag(v_x_46_) == 1)
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_57_; 
lean_dec(v_h__3_50_);
v_head_53_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_tail_54_);
lean_dec_ref_known(v_x_45_, 2);
v_head_55_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_55_);
v_tail_56_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_tail_56_);
lean_dec_ref_known(v_x_46_, 2);
v___x_57_ = lean_apply_5(v_h__2_49_, v_head_53_, v_tail_54_, v_head_55_, v_tail_56_, v_x_47_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; 
lean_dec(v_h__2_49_);
v___x_58_ = lean_apply_5(v_h__3_50_, v_x_45_, v_x_46_, v_x_47_, lean_box(0), lean_box(0));
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_, lean_object* v_h__3_66_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_dec(v_h__2_65_);
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_67_; 
lean_dec(v_h__3_66_);
v___x_67_ = lean_apply_1(v_h__1_64_, v_x_63_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
lean_dec(v_h__1_64_);
v___x_68_ = lean_apply_5(v_h__3_66_, v_x_61_, v_x_62_, v_x_63_, lean_box(0), lean_box(0));
return v___x_68_;
}
}
else
{
lean_dec(v_h__1_64_);
if (lean_obj_tag(v_x_62_) == 1)
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_73_; 
lean_dec(v_h__3_66_);
v_head_69_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_61_, 2);
v_head_71_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_head_71_);
v_tail_72_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_tail_72_);
lean_dec_ref_known(v_x_62_, 2);
v___x_73_ = lean_apply_5(v_h__2_65_, v_head_69_, v_tail_70_, v_head_71_, v_tail_72_, v_x_63_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; 
lean_dec(v_h__2_65_);
v___x_74_ = lean_apply_5(v_h__3_66_, v_x_61_, v_x_62_, v_x_63_, lean_box(0), lean_box(0));
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_76_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_76_);
v_val_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_x_75_, 1);
v___x_81_ = lean_apply_1(v_h__2_77_, v_val_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__2_86_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__1_85_, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_85_);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_x_84_, 1);
v___x_90_ = lean_apply_1(v_h__2_86_, v_val_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__1_92_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__2_93_, v___x_94_);
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_93_);
v_val_96_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_val_96_);
lean_dec_ref_known(v_x_91_, 1);
v___x_97_ = lean_apply_1(v_h__1_92_, v_val_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_98_, lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_101_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__2_102_, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; 
lean_dec(v_h__2_102_);
v_val_105_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v_x_100_, 1);
v___x_106_ = lean_apply_1(v_h__1_101_, v_val_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_109_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__1_108_, v___x_110_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_108_);
v_val_112_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v_x_107_, 1);
v___x_113_ = lean_apply_1(v_h__2_109_, v_val_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_114_, lean_object* v_motive_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_118_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_apply_1(v_h__1_117_, v___x_119_);
return v___x_120_;
}
else
{
lean_object* v_val_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_117_);
v_val_121_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v_x_116_, 1);
v___x_122_ = lean_apply_1(v_h__2_118_, v_val_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_124_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__2_125_, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_125_);
v_val_128_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v_x_123_, 1);
v___x_129_ = lean_apply_1(v_h__1_124_, v_val_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_130_, lean_object* v_motive_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_133_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__2_134_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_134_);
v_val_137_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_val_137_);
lean_dec_ref_known(v_x_132_, 1);
v___x_138_ = lean_apply_1(v_h__1_133_, v_val_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg___lam__0(lean_object* v_x_139_, lean_object* v_y_140_, lean_object* v_hy_141_, lean_object* v_x_142_, lean_object* v_hx_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_4(v_x_139_, v_y_140_, v_hy_141_, v_x_142_, lean_box(0));
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn___redArg(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_dec(v_x_149_);
lean_dec(v_x_147_);
lean_dec(v_x_146_);
return v_x_148_;
}
else
{
lean_object* v_head_150_; lean_object* v_tail_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_head_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc_n(v_head_150_, 2);
v_tail_151_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_tail_151_);
lean_dec_ref_known(v_x_145_, 2);
lean_inc(v_x_149_);
v___f_152_ = lean_alloc_closure((void*)(l_List_foldlRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_152_, 0, v_x_149_);
lean_inc(v_x_146_);
lean_inc(v_x_147_);
v___x_153_ = lean_apply_2(v_x_146_, v_x_147_, v_head_150_);
v___x_154_ = lean_apply_4(v_x_149_, v_x_147_, v_x_148_, v_head_150_, lean_box(0));
v_x_145_ = v_tail_151_;
v_x_147_ = v___x_153_;
v_x_148_ = v___x_154_;
v_x_149_ = v___f_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlRecOn(lean_object* v_00_u03b2_156_, lean_object* v_00_u03b1_157_, lean_object* v_motive_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_List_foldlRecOn___redArg(v_x_159_, v_x_160_, v_x_161_, v_x_162_, v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___lam__0(lean_object* v_x_165_, lean_object* v_b_166_, lean_object* v_c_167_, lean_object* v_a_168_, lean_object* v_m_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_4(v_x_165_, v_b_166_, v_c_167_, v_a_168_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(lean_object* v_x_171_, lean_object* v_init_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_dec(v_x_171_);
lean_inc(v_init_172_);
return v_init_172_;
}
else
{
lean_object* v_head_174_; lean_object* v_tail_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_head_174_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_174_);
v_tail_175_ = lean_ctor_get(v_x_173_, 1);
lean_inc(v_tail_175_);
lean_dec_ref_known(v_x_173_, 2);
lean_inc(v_x_171_);
v___x_176_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_171_, v_init_172_, v_tail_175_);
v___x_177_ = lean_apply_2(v_x_171_, v_head_174_, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(lean_object* v_x_178_, lean_object* v_init_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_178_, v_init_179_, v_x_180_);
lean_dec(v_init_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_dec(v_x_186_);
lean_dec(v_x_183_);
lean_inc(v_x_185_);
return v_x_185_;
}
else
{
lean_object* v_head_187_; lean_object* v_tail_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_head_187_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_head_187_);
v_tail_188_ = lean_ctor_get(v_x_182_, 1);
lean_inc_n(v_tail_188_, 2);
lean_dec_ref_known(v_x_182_, 2);
lean_inc(v_x_186_);
v___f_189_ = lean_alloc_closure((void*)(l_List_foldrRecOn___redArg___lam__0), 5, 1);
lean_closure_set(v___f_189_, 0, v_x_186_);
lean_inc(v_x_183_);
v___x_190_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_183_, v_x_184_, v_tail_188_);
v___x_191_ = l_List_foldrRecOn___redArg(v_tail_188_, v_x_183_, v_x_184_, v_x_185_, v___f_189_);
v___x_192_ = lean_apply_4(v_x_186_, v___x_190_, v___x_191_, v_head_187_, lean_box(0));
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_List_foldrRecOn___redArg(v_x_193_, v_x_194_, v_x_195_, v_x_196_, v_x_197_);
lean_dec(v_x_196_);
lean_dec(v_x_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn(lean_object* v_00_u03b2_199_, lean_object* v_00_u03b1_200_, lean_object* v_motive_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_List_foldrRecOn___redArg(v_x_202_, v_x_203_, v_x_204_, v_x_205_, v_x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOn___boxed(lean_object* v_00_u03b2_208_, lean_object* v_00_u03b1_209_, lean_object* v_motive_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_List_foldrRecOn(v_00_u03b2_208_, v_00_u03b1_209_, v_motive_210_, v_x_211_, v_x_212_, v_x_213_, v_x_214_, v_x_215_);
lean_dec(v_x_214_);
lean_dec(v_x_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_init_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_219_, v_init_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_x_225_, lean_object* v_init_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_List_foldr___at___00List_foldrRecOn_spec__0(v_00_u03b1_223_, v_00_u03b2_224_, v_x_225_, v_init_226_, v_x_227_);
lean_dec(v_init_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_, lean_object* v_h__3_232_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__3_232_);
lean_dec(v_h__2_231_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__1_230_, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_tail_235_; 
lean_dec(v_h__1_230_);
v_tail_235_ = lean_ctor_get(v_x_229_, 1);
if (lean_obj_tag(v_tail_235_) == 0)
{
lean_object* v_head_236_; lean_object* v___x_237_; 
lean_dec(v_h__3_232_);
v_head_236_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_head_236_);
lean_dec_ref_known(v_x_229_, 2);
v___x_237_ = lean_apply_1(v_h__2_231_, v_head_236_);
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v___x_239_; 
lean_inc(v_tail_235_);
lean_dec(v_h__2_231_);
v_head_238_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_head_238_);
lean_dec_ref_known(v_x_229_, 2);
v___x_239_ = lean_apply_3(v_h__3_232_, v_head_238_, v_tail_235_, lean_box(0));
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_, lean_object* v_h__3_245_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__3_245_);
lean_dec(v_h__2_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__1_243_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v_tail_248_; 
lean_dec(v_h__1_243_);
v_tail_248_ = lean_ctor_get(v_x_242_, 1);
if (lean_obj_tag(v_tail_248_) == 0)
{
lean_object* v_head_249_; lean_object* v___x_250_; 
lean_dec(v_h__3_245_);
v_head_249_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_head_249_);
lean_dec_ref_known(v_x_242_, 2);
v___x_250_ = lean_apply_1(v_h__2_244_, v_head_249_);
return v___x_250_;
}
else
{
lean_object* v_head_251_; lean_object* v___x_252_; 
lean_inc(v_tail_248_);
lean_dec(v_h__2_244_);
v_head_251_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_head_251_);
lean_dec_ref_known(v_x_242_, 2);
v___x_252_ = lean_apply_3(v_h__3_245_, v_head_251_, v_tail_248_, lean_box(0));
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_, lean_object* v_h__3_258_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_259_; 
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
v___x_259_ = lean_apply_2(v_h__1_256_, v_x_254_, v_x_255_);
return v___x_259_;
}
else
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v_zero_262_; uint8_t v_isZero_263_; 
lean_dec(v_h__1_256_);
v_head_260_ = lean_ctor_get(v_x_253_, 0);
v_tail_261_ = lean_ctor_get(v_x_253_, 1);
v_zero_262_ = lean_unsigned_to_nat(0u);
v_isZero_263_ = lean_nat_dec_eq(v_x_254_, v_zero_262_);
if (v_isZero_263_ == 0)
{
lean_object* v_one_264_; lean_object* v_n_265_; lean_object* v___x_266_; 
lean_inc(v_tail_261_);
lean_inc(v_head_260_);
lean_dec_ref_known(v_x_253_, 2);
lean_dec(v_h__3_258_);
v_one_264_ = lean_unsigned_to_nat(1u);
v_n_265_ = lean_nat_sub(v_x_254_, v_one_264_);
lean_dec(v_x_254_);
v___x_266_ = lean_apply_4(v_h__2_257_, v_head_260_, v_tail_261_, v_n_265_, v_x_255_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v_h__2_257_);
v___x_267_ = lean_apply_5(v_h__3_258_, v_x_253_, v_x_254_, v_x_255_, lean_box(0), lean_box(0));
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(lean_object* v_00_u03b1_268_, lean_object* v_motive_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_, lean_object* v_h__3_275_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v___x_276_; 
lean_dec(v_h__3_275_);
lean_dec(v_h__2_274_);
v___x_276_ = lean_apply_2(v_h__1_273_, v_x_271_, v_x_272_);
return v___x_276_;
}
else
{
lean_object* v_head_277_; lean_object* v_tail_278_; lean_object* v_zero_279_; uint8_t v_isZero_280_; 
lean_dec(v_h__1_273_);
v_head_277_ = lean_ctor_get(v_x_270_, 0);
v_tail_278_ = lean_ctor_get(v_x_270_, 1);
v_zero_279_ = lean_unsigned_to_nat(0u);
v_isZero_280_ = lean_nat_dec_eq(v_x_271_, v_zero_279_);
if (v_isZero_280_ == 0)
{
lean_object* v_one_281_; lean_object* v_n_282_; lean_object* v___x_283_; 
lean_inc(v_tail_278_);
lean_inc(v_head_277_);
lean_dec_ref_known(v_x_270_, 2);
lean_dec(v_h__3_275_);
v_one_281_ = lean_unsigned_to_nat(1u);
v_n_282_ = lean_nat_sub(v_x_271_, v_one_281_);
lean_dec(v_x_271_);
v___x_283_ = lean_apply_4(v_h__2_274_, v_head_277_, v_tail_278_, v_n_282_, v_x_272_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
lean_dec(v_h__2_274_);
v___x_284_ = lean_apply_5(v_h__3_275_, v_x_270_, v_x_271_, v_x_272_, lean_box(0), lean_box(0));
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v___x_289_; 
lean_dec(v_h__2_288_);
v___x_289_ = lean_apply_1(v_h__1_287_, v_x_286_);
return v___x_289_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v___x_292_; 
lean_dec(v_h__1_287_);
v_head_290_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_head_290_);
v_tail_291_ = lean_ctor_get(v_x_285_, 1);
lean_inc(v_tail_291_);
lean_dec_ref_known(v_x_285_, 2);
v___x_292_ = lean_apply_3(v_h__2_288_, v_head_290_, v_tail_291_, v_x_286_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_293_, lean_object* v_motive_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v___x_299_; 
lean_dec(v_h__2_298_);
v___x_299_ = lean_apply_1(v_h__1_297_, v_x_296_);
return v___x_299_;
}
else
{
lean_object* v_head_300_; lean_object* v_tail_301_; lean_object* v___x_302_; 
lean_dec(v_h__1_297_);
v_head_300_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_head_300_);
v_tail_301_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_tail_301_);
lean_dec_ref_known(v_x_295_, 2);
v___x_302_ = lean_apply_3(v_h__2_298_, v_head_300_, v_tail_301_, v_x_296_);
return v___x_302_;
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
