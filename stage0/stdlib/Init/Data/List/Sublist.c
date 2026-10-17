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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isPrefixOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isPrefixOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_6_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_6_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_6_;
}
else
{
lean_dec(v_h__1_3_);
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_7_; 
lean_dec(v_h__3_5_);
v___x_7_ = lean_apply_2(v_h__2_4_, v_x_1_, lean_box(0));
return v___x_7_;
}
else
{
lean_object* v_head_8_; lean_object* v_tail_9_; lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_12_; 
lean_dec(v_h__2_4_);
v_head_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_8_);
v_tail_9_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_9_);
lean_dec_ref_known(v_x_1_, 2);
v_head_10_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_10_);
v_tail_11_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_11_);
lean_dec_ref_known(v_x_2_, 2);
v___x_12_ = lean_apply_4(v_h__3_5_, v_head_8_, v_tail_9_, v_head_10_, v_tail_11_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v___x_20_ = lean_apply_1(v_h__1_17_, v_x_16_);
return v___x_20_;
}
else
{
lean_dec(v_h__1_17_);
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v___x_21_; 
lean_dec(v_h__3_19_);
v___x_21_ = lean_apply_2(v_h__2_18_, v_x_15_, lean_box(0));
return v___x_21_;
}
else
{
lean_object* v_head_22_; lean_object* v_tail_23_; lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_18_);
v_head_22_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_head_22_);
v_tail_23_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_tail_23_);
lean_dec_ref_known(v_x_15_, 2);
v_head_24_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_tail_25_);
lean_dec_ref_known(v_x_16_, 2);
v___x_26_ = lean_apply_4(v_h__3_19_, v_head_22_, v_tail_23_, v_head_24_, v_tail_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg(){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg___boxed(lean_object* v___dummy_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_List_instTransSubsetMem___redArg();
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object* v_00_u03b1_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg___boxed(lean_object* v___dummy_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_List_instTransSubset___redArg();
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object* v_00_u03b1_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg___boxed(lean_object* v___dummy_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_List_instTransSublist___redArg();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object* v_00_u03b1_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg(){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_List_instTransSublistSubset___redArg();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object* v_00_u03b1_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg___boxed(lean_object* v___dummy_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_List_instTransSubsetSublist___redArg();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object* v_00_u03b1_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg(){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg___boxed(lean_object* v___dummy_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_List_instTransSublistMem___redArg();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object* v_00_u03b1_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_65_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__1_64_, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; 
lean_dec(v_h__1_64_);
v_val_68_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v_x_63_, 1);
v___x_69_ = lean_apply_1(v_h__2_65_, v_val_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_70_, lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__2_74_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__1_73_, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v_val_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_73_);
v_val_77_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_x_72_, 1);
v___x_78_ = lean_apply_1(v_h__2_74_, v_val_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_84_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
v___x_84_ = lean_apply_1(v_h__1_81_, v_x_80_);
return v___x_84_;
}
else
{
lean_dec(v_h__1_81_);
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_85_; 
lean_dec(v_h__3_83_);
v___x_85_ = lean_apply_2(v_h__2_82_, v_x_79_, lean_box(0));
return v___x_85_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_82_);
v_head_86_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_tail_87_);
lean_dec_ref_known(v_x_79_, 2);
v_head_88_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_head_88_);
v_tail_89_ = lean_ctor_get(v_x_80_, 1);
lean_inc(v_tail_89_);
lean_dec_ref_known(v_x_80_, 2);
v___x_90_ = lean_apply_4(v_h__3_83_, v_head_86_, v_tail_87_, v_head_88_, v_tail_89_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(lean_object* v_00_u03b1_91_, lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_, lean_object* v_h__3_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_98_; 
lean_dec(v_h__3_97_);
lean_dec(v_h__2_96_);
v___x_98_ = lean_apply_1(v_h__1_95_, v_x_94_);
return v___x_98_;
}
else
{
lean_dec(v_h__1_95_);
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_99_; 
lean_dec(v_h__3_97_);
v___x_99_ = lean_apply_2(v_h__2_96_, v_x_93_, lean_box(0));
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_96_);
v_head_100_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_tail_101_);
lean_dec_ref_known(v_x_93_, 2);
v_head_102_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_x_94_, 1);
lean_inc(v_tail_103_);
lean_dec_ref_known(v_x_94_, 2);
v___x_104_ = lean_apply_4(v_h__3_97_, v_head_100_, v_tail_101_, v_head_102_, v_tail_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object* v_inst_105_, lean_object* v_l_u2081_106_, lean_object* v_l_u2082_107_){
_start:
{
lean_object* v___f_108_; uint8_t v___x_109_; 
v___f_108_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_108_, 0, v_inst_105_);
v___x_109_ = l_List_isSublist___redArg(v___f_108_, v_l_u2081_106_, v_l_u2082_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object* v_inst_110_, lean_object* v_l_u2081_111_, lean_object* v_l_u2082_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_110_, v_l_u2081_111_, v_l_u2082_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_l_u2081_117_, lean_object* v_l_u2082_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_116_, v_l_u2081_117_, v_l_u2082_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object* v_00_u03b1_120_, lean_object* v_inst_121_, lean_object* v_l_u2081_122_, lean_object* v_l_u2082_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_List_instDecidableSublistOfDecidableEq(v_00_u03b1_120_, v_inst_121_, v_l_u2081_122_, v_l_u2082_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_, lean_object* v_h__3_129_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__3_129_);
lean_dec(v_h__2_128_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__1_127_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v_tail_132_; 
lean_dec(v_h__1_127_);
v_tail_132_ = lean_ctor_get(v_x_126_, 1);
if (lean_obj_tag(v_tail_132_) == 0)
{
lean_object* v_head_133_; lean_object* v___x_134_; 
lean_dec(v_h__3_129_);
v_head_133_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_head_133_);
lean_dec_ref_known(v_x_126_, 2);
v___x_134_ = lean_apply_1(v_h__2_128_, v_head_133_);
return v___x_134_;
}
else
{
lean_object* v_head_135_; lean_object* v___x_136_; 
lean_inc(v_tail_132_);
lean_dec(v_h__2_128_);
v_head_135_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_head_135_);
lean_dec_ref_known(v_x_126_, 2);
v___x_136_ = lean_apply_3(v_h__3_129_, v_head_135_, v_tail_132_, lean_box(0));
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_137_, lean_object* v_motive_138_, lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_, lean_object* v_h__3_142_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__2_141_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_apply_1(v_h__1_140_, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v_tail_145_; 
lean_dec(v_h__1_140_);
v_tail_145_ = lean_ctor_get(v_x_139_, 1);
if (lean_obj_tag(v_tail_145_) == 0)
{
lean_object* v_head_146_; lean_object* v___x_147_; 
lean_dec(v_h__3_142_);
v_head_146_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_head_146_);
lean_dec_ref_known(v_x_139_, 2);
v___x_147_ = lean_apply_1(v_h__2_141_, v_head_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v___x_149_; 
lean_inc(v_tail_145_);
lean_dec(v_h__2_141_);
v_head_148_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_head_148_);
lean_dec_ref_known(v_x_139_, 2);
v___x_149_ = lean_apply_3(v_h__3_142_, v_head_148_, v_tail_145_, lean_box(0));
return v___x_149_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object* v_inst_150_, lean_object* v_l_u2081_151_, lean_object* v_l_u2082_152_){
_start:
{
lean_object* v___f_153_; uint8_t v___x_154_; 
v___f_153_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_153_, 0, v_inst_150_);
v___x_154_ = l_List_isPrefixOf___redArg(v___f_153_, v_l_u2081_151_, v_l_u2082_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object* v_inst_155_, lean_object* v_l_u2081_156_, lean_object* v_l_u2082_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_155_, v_l_u2081_156_, v_l_u2082_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_l_u2081_162_, lean_object* v_l_u2082_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_161_, v_l_u2081_162_, v_l_u2082_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_l_u2081_167_, lean_object* v_l_u2082_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_List_instDecidableIsPrefixOfDecidableEq(v_00_u03b1_165_, v_inst_166_, v_l_u2081_167_, v_l_u2082_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object* v_inst_171_, lean_object* v_l_u2081_172_, lean_object* v_l_u2082_173_){
_start:
{
lean_object* v___f_174_; uint8_t v___x_175_; 
v___f_174_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_174_, 0, v_inst_171_);
v___x_175_ = l_List_isSuffixOf___redArg(v___f_174_, v_l_u2081_172_, v_l_u2082_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object* v_inst_176_, lean_object* v_l_u2081_177_, lean_object* v_l_u2082_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_176_, v_l_u2081_177_, v_l_u2082_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_l_u2081_183_, lean_object* v_l_u2082_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_182_, v_l_u2081_183_, v_l_u2082_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_l_u2081_188_, lean_object* v_l_u2082_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_List_instDecidableIsSuffixOfDecidableEq(v_00_u03b1_186_, v_inst_187_, v_l_u2081_188_, v_l_u2082_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object* v_inst_192_, lean_object* v_l_u2081_193_, lean_object* v_l_u2082_194_){
_start:
{
lean_object* v___f_195_; uint8_t v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_195_, 0, v_inst_192_);
v___x_196_ = l_List_isInfixOf__internal___redArg(v___f_195_, v_l_u2081_193_, v_l_u2082_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object* v_inst_197_, lean_object* v_l_u2081_198_, lean_object* v_l_u2082_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_197_, v_l_u2081_198_, v_l_u2082_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_l_u2081_204_, lean_object* v_l_u2082_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_203_, v_l_u2081_204_, v_l_u2082_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object* v_00_u03b1_207_, lean_object* v_inst_208_, lean_object* v_l_u2081_209_, lean_object* v_l_u2082_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_List_instDecidableIsInfixOfDecidableEq(v_00_u03b1_207_, v_inst_208_, v_l_u2081_209_, v_l_u2082_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
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
