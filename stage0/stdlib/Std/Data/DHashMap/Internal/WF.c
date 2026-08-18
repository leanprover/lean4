// Lean compiler output
// Module: Std.Data.DHashMap.Internal.WF
// Imports: import all Std.Data.Internal.List.Associative import all Std.Data.DHashMap.Raw import all Std.Data.DHashMap.RawDef import all Std.Data.DHashMap.Internal.AssocList.Basic import all Std.Data.DHashMap.Internal.Defs public import Std.Data.DHashMap.Internal.Model import Init.Data.Array.Bootstrap import Init.Data.Array.Lemmas import Init.Data.Array.MapIdx import Init.Data.List.Perm import Init.Omega
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeDistance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeDistance___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Option_get_x21_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Option_get_x21_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_2_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_object* v___x_8_; 
lean_dec(v_h__2_5_);
v___x_8_ = lean_apply_3(v_h__1_4_, v_x_1_, v_x_3_, lean_box(0));
return v___x_8_;
}
else
{
lean_object* v_one_9_; lean_object* v_n_10_; lean_object* v___x_11_; 
lean_dec(v_h__1_4_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_n_10_ = lean_nat_sub(v_x_2_, v_one_9_);
v___x_11_ = lean_apply_4(v_h__2_5_, v_x_1_, v_n_10_, v_x_3_, lean_box(0));
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___redArg___boxed(lean_object* v_x_12_, lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___redArg(v_x_12_, v_x_13_, v_x_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_x_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_m_20_, lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_x_23_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec(v_h__2_27_);
v___x_30_ = lean_apply_3(v_h__1_26_, v_x_22_, v_x_24_, lean_box(0));
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_26_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_x_23_, v_one_31_);
v___x_33_ = lean_apply_4(v_h__2_27_, v_x_22_, v_n_32_, v_x_24_, lean_box(0));
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_m_36_, lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__5_splitter(v_00_u03b1_34_, v_00_u03b2_35_, v_m_36_, v_motive_37_, v_x_38_, v_x_39_, v_x_40_, v_x_41_, v_h__1_42_, v_h__2_43_);
lean_dec(v_x_39_);
lean_dec_ref(v_m_36_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter___redArg(lean_object* v_firstEmpty_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_firstEmpty_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_val_50_ = lean_ctor_get(v_firstEmpty_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref_known(v_firstEmpty_45_, 1);
v___x_51_ = lean_apply_1(v_h__2_47_, v_val_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_m_54_, lean_object* v_motive_55_, lean_object* v_firstEmpty_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_firstEmpty_56_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_57_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_57_);
v_val_61_ = lean_ctor_get(v_firstEmpty_56_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v_firstEmpty_56_, 1);
v___x_62_ = lean_apply_1(v_h__2_58_, v_val_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter___boxed(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_m_65_, lean_object* v_motive_66_, lean_object* v_firstEmpty_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__1_splitter(v_00_u03b1_63_, v_00_u03b2_64_, v_m_65_, v_motive_66_, v_firstEmpty_67_, v_h__1_68_, v_h__2_69_);
lean_dec_ref(v_m_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__3_splitter___redArg(lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
uint8_t v_isSome_74_; 
v_isSome_74_ = lean_noption_is_some(v_x_71_);
if (v_isSome_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__2_73_);
lean_dec(v_x_71_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__1_72_, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v_val_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_72_);
v_val_77_ = lean_noption_get(v_x_71_);
v___x_78_ = lean_apply_1(v_h__2_73_, v_val_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_probeFromAux_match__3_splitter(lean_object* v_00_u03b1_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
uint8_t v_isSome_84_; 
v_isSome_84_ = lean_noption_is_some(v_x_81_);
if (v_isSome_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_h__2_83_);
lean_dec(v_x_81_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_1(v_h__1_82_, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_82_);
v_val_87_ = lean_noption_get(v_x_81_);
v___x_88_ = lean_apply_1(v_h__2_83_, v_val_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter___redArg(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__2_91_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__1_90_, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_97_; 
lean_dec(v_h__1_90_);
v_val_94_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v_x_89_, 1);
v_fst_95_ = lean_ctor_get(v_val_94_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v_val_94_, 1);
lean_inc(v_snd_96_);
lean_dec(v_val_94_);
v___x_97_ = lean_apply_2(v_h__2_91_, v_fst_95_, v_snd_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
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
lean_object* v_val_106_; lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_102_);
v_val_106_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v_x_101_, 1);
v_fst_107_ = lean_ctor_get(v_val_106_, 0);
lean_inc(v_fst_107_);
v_snd_108_ = lean_ctor_get(v_val_106_, 1);
lean_inc(v_snd_108_);
lean_dec(v_val_106_);
v___x_109_ = lean_apply_2(v_h__2_103_, v_fst_107_, v_snd_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg(lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v_key_111_; lean_object* v_value_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_key_111_ = lean_ctor_get(v_x_110_, 1);
v_value_112_ = lean_ctor_get(v_x_110_, 2);
lean_inc(v_value_112_);
lean_inc(v_key_111_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_key_111_);
lean_ctor_set(v___x_113_, 1, v_value_112_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg___boxed(lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg(v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_inst_120_, lean_object* v_query_121_, lean_object* v_n_122_, lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DHashMap_Internal_scanResultEntry_x3f___redArg(v_x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultEntry_x3f___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_query_128_, lean_object* v_n_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DHashMap_Internal_scanResultEntry_x3f(v_00_u03b1_125_, v_00_u03b2_126_, v_inst_127_, v_query_128_, v_n_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_n_129_);
lean_dec(v_query_128_);
lean_dec_ref(v_inst_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg(lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_value_133_; lean_object* v___x_134_; 
v_value_133_ = lean_ctor_get(v_x_132_, 2);
lean_inc(v_value_133_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_value_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg___boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg(v_x_136_);
lean_dec(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_query_142_, lean_object* v_n_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DHashMap_Internal_scanResultValueCast_x3f___redArg(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scanResultValueCast_x3f___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_query_150_, lean_object* v_n_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_DHashMap_Internal_scanResultValueCast_x3f(v_00_u03b1_146_, v_00_u03b2_147_, v_inst_148_, v_inst_149_, v_query_150_, v_n_151_, v_x_152_);
lean_dec(v_x_152_);
lean_dec(v_n_151_);
lean_dec(v_query_150_);
lean_dec_ref(v_inst_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeDistance(lean_object* v_n_154_, lean_object* v_i_155_, lean_object* v_target_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_le(v_i_155_, v_target_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_nat_sub(v_n_154_, v_i_155_);
v___x_159_ = lean_nat_add(v___x_158_, v_target_156_);
lean_dec(v___x_158_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_nat_sub(v_target_156_, v_i_155_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeDistance___boxed(lean_object* v_n_161_, lean_object* v_i_162_, lean_object* v_target_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeDistance(v_n_161_, v_i_162_, v_target_163_);
lean_dec(v_target_163_);
lean_dec(v_i_162_);
lean_dec(v_n_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter___redArg(lean_object* v_firstEmpty_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
if (lean_obj_tag(v_firstEmpty_165_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__2_167_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__1_166_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_166_);
v_val_170_ = lean_ctor_get(v_firstEmpty_165_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v_firstEmpty_165_, 1);
v___x_171_ = lean_apply_1(v_h__2_167_, v_val_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter(lean_object* v_00_u03b1_172_, lean_object* v_00_u03b2_173_, lean_object* v_m_174_, lean_object* v_motive_175_, lean_object* v_firstEmpty_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
if (lean_obj_tag(v_firstEmpty_176_) == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_178_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__1_177_, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_177_);
v_val_181_ = lean_ctor_get(v_firstEmpty_176_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_firstEmpty_176_, 1);
v___x_182_ = lean_apply_1(v_h__2_178_, v_val_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter___boxed(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_motive_186_, lean_object* v_firstEmpty_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_probeFromAux__found__of__path_match__1__2_splitter(v_00_u03b1_183_, v_00_u03b2_184_, v_m_185_, v_motive_186_, v_firstEmpty_187_, v_h__1_188_, v_h__2_189_);
lean_dec_ref(v_m_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter___redArg(lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v_index_194_; lean_object* v_key_195_; lean_object* v_value_196_; lean_object* v___x_197_; 
lean_dec(v_h__2_193_);
v_index_194_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_index_194_);
v_key_195_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_key_195_);
v_value_196_ = lean_ctor_get(v_x_191_, 2);
lean_inc(v_value_196_);
lean_dec_ref_known(v_x_191_, 3);
v___x_197_ = lean_apply_4(v_h__1_192_, v_index_194_, v_key_195_, v_value_196_, lean_box(0));
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_192_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_1(v_h__2_193_, v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_inst_202_, lean_object* v_query_203_, lean_object* v_n_204_, lean_object* v_motive_205_, lean_object* v_x_206_, lean_object* v_h__1_207_, lean_object* v_h__2_208_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v_index_209_; lean_object* v_key_210_; lean_object* v_value_211_; lean_object* v___x_212_; 
lean_dec(v_h__2_208_);
v_index_209_ = lean_ctor_get(v_x_206_, 0);
lean_inc(v_index_209_);
v_key_210_ = lean_ctor_get(v_x_206_, 1);
lean_inc(v_key_210_);
v_value_211_ = lean_ctor_get(v_x_206_, 2);
lean_inc(v_value_211_);
lean_dec_ref_known(v_x_206_, 3);
v___x_212_ = lean_apply_4(v_h__1_207_, v_index_209_, v_key_210_, v_value_211_, lean_box(0));
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_207_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__2_208_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_query_218_, lean_object* v_n_219_, lean_object* v_motive_220_, lean_object* v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_scanResultEntry_x3f_match__1_splitter(v_00_u03b1_215_, v_00_u03b2_216_, v_inst_217_, v_query_218_, v_n_219_, v_motive_220_, v_x_221_, v_h__1_222_, v_h__2_223_);
lean_dec(v_n_219_);
lean_dec(v_query_218_);
lean_dec_ref(v_inst_217_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_h__1_226_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_h__2_227_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_dec(v_h__2_227_);
v_val_230_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v_x_225_, 1);
v___x_231_ = lean_apply_1(v_h__1_226_, v_val_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_232_, lean_object* v_motive_233_, lean_object* v_x_234_, lean_object* v_h__1_235_, lean_object* v_h__2_236_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_h__1_235_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_1(v_h__2_236_, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; 
lean_dec(v_h__2_236_);
v_val_239_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v_x_234_, 1);
v___x_240_ = lean_apply_1(v_h__1_235_, v_val_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_245_; 
lean_dec(v_h__2_243_);
v_a_244_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v_x_241_, 1);
v___x_245_ = lean_apply_1(v_h__1_242_, v_a_244_);
return v___x_245_;
}
else
{
lean_object* v_a_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_242_);
v_a_246_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v_x_241_, 1);
v___x_247_ = lean_apply_1(v_h__2_243_, v_a_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_248_, lean_object* v_motive_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; 
lean_dec(v_h__2_252_);
v_a_253_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v_x_250_, 1);
v___x_254_ = lean_apply_1(v_h__1_251_, v_a_253_);
return v___x_254_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_256_; 
lean_dec(v_h__1_251_);
v_a_255_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v_x_250_, 1);
v___x_256_ = lean_apply_1(v_h__2_252_, v_a_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__5_splitter___redArg(lean_object* v_x_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
_start:
{
uint8_t v_isSome_260_; 
v_isSome_260_ = lean_noption_is_some(v_x_257_);
if (v_isSome_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v_h__2_259_);
lean_dec(v_x_257_);
v___x_261_ = lean_apply_1(v_h__1_258_, lean_box(0));
return v___x_261_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_258_);
v_val_262_ = lean_noption_get(v_x_257_);
v___x_263_ = lean_apply_2(v_h__2_259_, v_val_262_, lean_box(0));
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__5_splitter(lean_object* v_00_u03b1_264_, lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
uint8_t v_isSome_269_; 
v_isSome_269_ = lean_noption_is_some(v_x_266_);
if (v_isSome_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v_h__2_268_);
lean_dec(v_x_266_);
v___x_270_ = lean_apply_1(v_h__1_267_, lean_box(0));
return v___x_270_;
}
else
{
lean_object* v_val_271_; lean_object* v___x_272_; 
lean_dec(v_h__1_267_);
v_val_271_ = lean_noption_get(v_x_266_);
v___x_272_ = lean_apply_2(v_h__2_268_, v_val_271_, lean_box(0));
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__3_splitter___redArg(lean_object* v_x_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
uint8_t v_isSome_276_; 
v_isSome_276_ = lean_noption_is_some(v_x_273_);
if (v_isSome_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_h__2_275_);
lean_dec(v_x_273_);
v___x_277_ = lean_apply_1(v_h__1_274_, lean_box(0));
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_274_);
v_val_278_ = lean_noption_get(v_x_273_);
v___x_279_ = lean_apply_2(v_h__2_275_, v_val_278_, lean_box(0));
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__3_splitter(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_motive_282_, lean_object* v_x_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_){
_start:
{
uint8_t v_isSome_286_; 
v_isSome_286_ = lean_noption_is_some(v_x_283_);
if (v_isSome_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec(v_h__2_285_);
lean_dec(v_x_283_);
v___x_287_ = lean_apply_1(v_h__1_284_, lean_box(0));
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_289_; 
lean_dec(v_h__1_284_);
v_val_288_ = lean_noption_get(v_x_283_);
v___x_289_ = lean_apply_2(v_h__2_285_, v_val_288_, lean_box(0));
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter___redArg(lean_object* v_x_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_h__2_292_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_1(v_h__1_291_, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; 
lean_dec(v_h__1_291_);
v_val_295_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v_x_290_, 1);
v___x_296_ = lean_apply_1(v_h__2_292_, v_val_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b3_298_, lean_object* v_k_299_, lean_object* v_motive_300_, lean_object* v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_h__2_303_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_h__1_302_, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; 
lean_dec(v_h__1_302_);
v_val_306_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v_x_301_, 1);
v___x_307_ = lean_apply_1(v_h__2_303_, v_val_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter___boxed(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b3_309_, lean_object* v_k_310_, lean_object* v_motive_311_, lean_object* v_x_312_, lean_object* v_h__1_313_, lean_object* v_h__2_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_filterMapStep_match__1_splitter(v_00_u03b1_308_, v_00_u03b3_309_, v_k_310_, v_motive_311_, v_x_312_, v_h__1_313_, v_h__2_314_);
lean_dec(v_k_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__2_318_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__1_317_, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_322_; 
lean_dec(v_h__1_317_);
v_val_321_ = lean_ctor_get(v_x_316_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v_x_316_, 1);
v___x_322_ = lean_apply_1(v_h__2_318_, v_val_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_323_, lean_object* v_motive_324_, lean_object* v_x_325_, lean_object* v_h__1_326_, lean_object* v_h__2_327_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_h__2_327_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_apply_1(v_h__1_326_, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v_val_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_326_);
v_val_330_ = lean_ctor_get(v_x_325_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v_x_325_, 1);
v___x_331_ = lean_apply_1(v_h__2_327_, v_val_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Option_get_x21_match__1_splitter___redArg(lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_h__1_333_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_1(v_h__2_334_, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v_val_337_; lean_object* v___x_338_; 
lean_dec(v_h__2_334_);
v_val_337_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v_x_332_, 1);
v___x_338_ = lean_apply_1(v_h__1_333_, v_val_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Option_get_x21_match__1_splitter(lean_object* v_00_u03b1_339_, lean_object* v_motive_340_, lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v_h__1_342_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_apply_1(v_h__2_343_, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v_val_346_; lean_object* v___x_347_; 
lean_dec(v_h__2_343_);
v_val_346_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v_x_341_, 1);
v___x_347_ = lean_apply_1(v_h__1_342_, v_val_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___redArg(lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_350_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_apply_1(v_h__1_349_, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v_val_353_; lean_object* v___x_354_; 
lean_dec(v_h__1_349_);
v_val_353_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_x_348_, 1);
v___x_354_ = lean_apply_1(v_h__2_350_, v_val_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_a_357_, lean_object* v_motive_358_, lean_object* v_x_359_, lean_object* v_h__1_360_, lean_object* v_h__2_361_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_h__2_361_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_apply_1(v_h__1_360_, v___x_362_);
return v___x_363_;
}
else
{
lean_object* v_val_364_; lean_object* v___x_365_; 
lean_dec(v_h__1_360_);
v_val_364_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_x_359_, 1);
v___x_365_ = lean_apply_1(v_h__2_361_, v_val_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___boxed(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_a_368_, lean_object* v_motive_369_, lean_object* v_x_370_, lean_object* v_h__1_371_, lean_object* v_h__2_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(v_00_u03b1_366_, v_00_u03b2_367_, v_a_368_, v_motive_369_, v_x_370_, v_h__1_371_, v_h__2_372_);
lean_dec(v_a_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(lean_object* v_x_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__2_376_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__1_375_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_380_; 
lean_dec(v_h__1_375_);
v_val_379_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v_x_374_, 1);
v___x_380_ = lean_apply_1(v_h__2_376_, v_val_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object* v_00_u03b2_381_, lean_object* v_motive_382_, lean_object* v_x_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_h__2_385_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_apply_1(v_h__1_384_, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; 
lean_dec(v_h__1_384_);
v_val_388_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_x_383_, 1);
v___x_389_ = lean_apply_1(v_h__2_385_, v_val_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__1_391_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_apply_1(v_h__2_392_, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_392_);
v_val_395_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_x_390_, 1);
v___x_396_ = lean_apply_1(v_h__1_391_, v_val_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_motive_399_, lean_object* v_x_400_, lean_object* v_h__1_401_, lean_object* v_h__2_402_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_h__1_401_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_apply_1(v_h__2_402_, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; 
lean_dec(v_h__2_402_);
v_val_405_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_x_400_, 1);
v___x_406_ = lean_apply_1(v_h__1_401_, v_val_405_);
return v___x_406_;
}
}
}
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_WF(builtin);
}
#ifdef __cplusplus
}
#endif
