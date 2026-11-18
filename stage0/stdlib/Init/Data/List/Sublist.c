// Lean compiler output
// Module: Init.Data.List.Sublist
// Imports: public import Init.BinderPredicates public import Init.Ext public import Init.PropLemmas import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.List.TakeDrop import Init.TacticsExtra
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isInfixOf__internal___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isSuffixOf___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isSublist___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg();
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg();
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg();
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg();
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg();
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg();
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_List_instTransSubsetMem___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg(){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_List_instTransSubset___redArg();
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object* v_00_u03b1_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_List_instTransSublist___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object* v_00_u03b1_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_List_instTransSublistSubset___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object* v_00_u03b1_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg(){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg___boxed(lean_object* v___dummy_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_List_instTransSubsetSublist___redArg();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object* v_00_u03b1_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg(){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_List_instTransSublistMem___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_38_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_38_);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v_x_37_, 1);
v___x_43_ = lean_apply_1(v_h__2_39_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_47_);
v_val_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v_x_46_, 1);
v___x_52_ = lean_apply_1(v_h__2_48_, v_val_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_58_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v___x_58_ = lean_apply_1(v_h__1_55_, v_x_54_);
return v___x_58_;
}
else
{
lean_dec(v_h__1_55_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_59_; 
lean_dec(v_h__3_57_);
v___x_59_ = lean_apply_2(v_h__2_56_, v_x_53_, lean_box(0));
return v___x_59_;
}
else
{
lean_object* v_head_60_; lean_object* v_tail_61_; lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_56_);
v_head_60_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_60_);
v_tail_61_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_61_);
lean_dec_ref_known(v_x_53_, 2);
v_head_62_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_62_);
v_tail_63_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_63_);
lean_dec_ref_known(v_x_54_, 2);
v___x_64_ = lean_apply_4(v_h__3_57_, v_head_60_, v_tail_61_, v_head_62_, v_tail_63_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(lean_object* v_00_u03b1_65_, lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_72_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__2_70_);
v___x_72_ = lean_apply_1(v_h__1_69_, v_x_68_);
return v___x_72_;
}
else
{
lean_dec(v_h__1_69_);
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_73_; 
lean_dec(v_h__3_71_);
v___x_73_ = lean_apply_2(v_h__2_70_, v_x_67_, lean_box(0));
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_70_);
v_head_74_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_tail_75_);
lean_dec_ref_known(v_x_67_, 2);
v_head_76_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_head_76_);
v_tail_77_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_tail_77_);
lean_dec_ref_known(v_x_68_, 2);
v___x_78_ = lean_apply_4(v_h__3_71_, v_head_74_, v_tail_75_, v_head_76_, v_tail_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object* v_inst_79_, lean_object* v_l_u2081_80_, lean_object* v_l_u2082_81_){
_start:
{
lean_object* v___f_82_; uint8_t v___x_83_; 
v___f_82_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_82_, 0, v_inst_79_);
v___x_83_ = l_List_isSublist___redArg(v___f_82_, v_l_u2081_80_, v_l_u2082_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object* v_inst_84_, lean_object* v_l_u2081_85_, lean_object* v_l_u2082_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_84_, v_l_u2081_85_, v_l_u2082_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_l_u2081_91_, lean_object* v_l_u2082_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_90_, v_l_u2081_91_, v_l_u2082_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_l_u2081_96_, lean_object* v_l_u2082_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_List_instDecidableSublistOfDecidableEq(v_00_u03b1_94_, v_inst_95_, v_l_u2081_96_, v_l_u2082_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object* v_inst_100_, lean_object* v_l_u2081_101_, lean_object* v_l_u2082_102_){
_start:
{
lean_object* v___f_103_; uint8_t v___x_104_; 
v___f_103_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_103_, 0, v_inst_100_);
v___x_104_ = l_List_isPrefixOf___redArg(v___f_103_, v_l_u2081_101_, v_l_u2082_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object* v_inst_105_, lean_object* v_l_u2081_106_, lean_object* v_l_u2082_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_105_, v_l_u2081_106_, v_l_u2082_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_l_u2081_112_, lean_object* v_l_u2082_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_111_, v_l_u2081_112_, v_l_u2082_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_l_u2081_117_, lean_object* v_l_u2082_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_List_instDecidableIsPrefixOfDecidableEq(v_00_u03b1_115_, v_inst_116_, v_l_u2081_117_, v_l_u2082_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object* v_inst_121_, lean_object* v_l_u2081_122_, lean_object* v_l_u2082_123_){
_start:
{
lean_object* v___f_124_; uint8_t v___x_125_; 
v___f_124_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_124_, 0, v_inst_121_);
v___x_125_ = l_List_isSuffixOf___redArg(v___f_124_, v_l_u2081_122_, v_l_u2082_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object* v_inst_126_, lean_object* v_l_u2081_127_, lean_object* v_l_u2082_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_126_, v_l_u2081_127_, v_l_u2082_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_l_u2081_133_, lean_object* v_l_u2082_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_132_, v_l_u2081_133_, v_l_u2082_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object* v_00_u03b1_136_, lean_object* v_inst_137_, lean_object* v_l_u2081_138_, lean_object* v_l_u2082_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_List_instDecidableIsSuffixOfDecidableEq(v_00_u03b1_136_, v_inst_137_, v_l_u2081_138_, v_l_u2082_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_150_, lean_object* v_motive_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__2_154_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_153_, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_153_);
v_head_157_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_head_157_);
v_tail_158_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_tail_158_);
lean_dec_ref_known(v_x_152_, 2);
v___x_159_ = lean_apply_2(v_h__2_154_, v_head_157_, v_tail_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object* v_inst_160_, lean_object* v_l_u2081_161_, lean_object* v_l_u2082_162_){
_start:
{
lean_object* v___f_163_; uint8_t v___x_164_; 
v___f_163_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_163_, 0, v_inst_160_);
v___x_164_ = l_List_isInfixOf__internal___redArg(v___f_163_, v_l_u2081_161_, v_l_u2082_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object* v_inst_165_, lean_object* v_l_u2081_166_, lean_object* v_l_u2082_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_165_, v_l_u2081_166_, v_l_u2082_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_l_u2081_172_, lean_object* v_l_u2082_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_171_, v_l_u2081_172_, v_l_u2082_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_l_u2081_177_, lean_object* v_l_u2082_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_List_instDecidableIsInfixOfDecidableEq(v_00_u03b1_175_, v_inst_176_, v_l_u2081_177_, v_l_u2082_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Sublist(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Sublist(builtin);
}
#ifdef __cplusplus
}
#endif
