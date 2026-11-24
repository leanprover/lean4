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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
lean_object* v_zero_83_; uint8_t v_isZero_84_; 
v_zero_83_ = lean_unsigned_to_nat(0u);
v_isZero_84_ = lean_nat_dec_eq(v_x_79_, v_zero_83_);
if (v_isZero_84_ == 1)
{
lean_object* v___x_85_; 
lean_dec(v_h__2_82_);
v___x_85_ = lean_apply_1(v_h__1_81_, v_x_80_);
return v___x_85_;
}
else
{
lean_object* v_one_86_; lean_object* v_n_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_81_);
v_one_86_ = lean_unsigned_to_nat(1u);
v_n_87_ = lean_nat_sub(v_x_79_, v_one_86_);
v___x_88_ = lean_apply_2(v_h__2_82_, v_n_87_, v_x_80_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_89_, lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___redArg(v_x_89_, v_x_90_, v_h__1_91_, v_h__2_92_);
lean_dec(v_x_89_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
lean_object* v_zero_100_; uint8_t v_isZero_101_; 
v_zero_100_ = lean_unsigned_to_nat(0u);
v_isZero_101_ = lean_nat_dec_eq(v_x_96_, v_zero_100_);
if (v_isZero_101_ == 1)
{
lean_object* v___x_102_; 
lean_dec(v_h__2_99_);
v___x_102_ = lean_apply_1(v_h__1_98_, v_x_97_);
return v___x_102_;
}
else
{
lean_object* v_one_103_; lean_object* v_n_104_; lean_object* v___x_105_; 
lean_dec(v_h__1_98_);
v_one_103_ = lean_unsigned_to_nat(1u);
v_n_104_ = lean_nat_sub(v_x_96_, v_one_103_);
v___x_105_ = lean_apply_2(v_h__2_99_, v_n_104_, v_x_97_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_106_, lean_object* v_motive_107_, lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_List_Sublist_0__List_replicate_match__1_splitter(v_00_u03b1_106_, v_motive_107_, v_x_108_, v_x_109_, v_h__1_110_, v_h__2_111_);
lean_dec(v_x_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_, lean_object* v_h__3_117_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_object* v___x_118_; 
lean_dec(v_h__3_117_);
lean_dec(v_h__2_116_);
v___x_118_ = lean_apply_1(v_h__1_115_, v_x_114_);
return v___x_118_;
}
else
{
lean_dec(v_h__1_115_);
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v___x_119_; 
lean_dec(v_h__3_117_);
v___x_119_ = lean_apply_2(v_h__2_116_, v_x_113_, lean_box(0));
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_116_);
v_head_120_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_head_120_);
v_tail_121_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_tail_121_);
lean_dec_ref_known(v_x_113_, 2);
v_head_122_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_tail_123_);
lean_dec_ref_known(v_x_114_, 2);
v___x_124_ = lean_apply_4(v_h__3_117_, v_head_120_, v_tail_121_, v_head_122_, v_tail_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(lean_object* v_00_u03b1_125_, lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_, lean_object* v_h__3_131_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_132_; 
lean_dec(v_h__3_131_);
lean_dec(v_h__2_130_);
v___x_132_ = lean_apply_1(v_h__1_129_, v_x_128_);
return v___x_132_;
}
else
{
lean_dec(v_h__1_129_);
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_133_; 
lean_dec(v_h__3_131_);
v___x_133_ = lean_apply_2(v_h__2_130_, v_x_127_, lean_box(0));
return v___x_133_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_130_);
v_head_134_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_head_134_);
v_tail_135_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_tail_135_);
lean_dec_ref_known(v_x_127_, 2);
v_head_136_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_136_);
v_tail_137_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_137_);
lean_dec_ref_known(v_x_128_, 2);
v___x_138_ = lean_apply_4(v_h__3_131_, v_head_134_, v_tail_135_, v_head_136_, v_tail_137_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object* v_inst_139_, lean_object* v_l_u2081_140_, lean_object* v_l_u2082_141_){
_start:
{
lean_object* v___f_142_; uint8_t v___x_143_; 
v___f_142_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_142_, 0, v_inst_139_);
v___x_143_ = l_List_isSublist___redArg(v___f_142_, v_l_u2081_140_, v_l_u2082_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object* v_inst_144_, lean_object* v_l_u2081_145_, lean_object* v_l_u2082_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_144_, v_l_u2081_145_, v_l_u2082_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object* v_00_u03b1_149_, lean_object* v_inst_150_, lean_object* v_l_u2081_151_, lean_object* v_l_u2082_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_150_, v_l_u2081_151_, v_l_u2082_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_l_u2081_156_, lean_object* v_l_u2082_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_List_instDecidableSublistOfDecidableEq(v_00_u03b1_154_, v_inst_155_, v_l_u2081_156_, v_l_u2082_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__1_161_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_tail_166_; 
lean_dec(v_h__1_161_);
v_tail_166_ = lean_ctor_get(v_x_160_, 1);
if (lean_obj_tag(v_tail_166_) == 0)
{
lean_object* v_head_167_; lean_object* v___x_168_; 
lean_dec(v_h__3_163_);
v_head_167_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_head_167_);
lean_dec_ref_known(v_x_160_, 2);
v___x_168_ = lean_apply_1(v_h__2_162_, v_head_167_);
return v___x_168_;
}
else
{
lean_object* v_head_169_; lean_object* v___x_170_; 
lean_inc(v_tail_166_);
lean_dec(v_h__2_162_);
v_head_169_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_head_169_);
lean_dec_ref_known(v_x_160_, 2);
v___x_170_ = lean_apply_3(v_h__3_163_, v_head_169_, v_tail_166_, lean_box(0));
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_171_, lean_object* v_motive_172_, lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_, lean_object* v_h__3_176_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__3_176_);
lean_dec(v_h__2_175_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__1_174_, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_tail_179_; 
lean_dec(v_h__1_174_);
v_tail_179_ = lean_ctor_get(v_x_173_, 1);
if (lean_obj_tag(v_tail_179_) == 0)
{
lean_object* v_head_180_; lean_object* v___x_181_; 
lean_dec(v_h__3_176_);
v_head_180_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_180_);
lean_dec_ref_known(v_x_173_, 2);
v___x_181_ = lean_apply_1(v_h__2_175_, v_head_180_);
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v___x_183_; 
lean_inc(v_tail_179_);
lean_dec(v_h__2_175_);
v_head_182_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_182_);
lean_dec_ref_known(v_x_173_, 2);
v___x_183_ = lean_apply_3(v_h__3_176_, v_head_182_, v_tail_179_, lean_box(0));
return v___x_183_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object* v_inst_184_, lean_object* v_l_u2081_185_, lean_object* v_l_u2082_186_){
_start:
{
lean_object* v___f_187_; uint8_t v___x_188_; 
v___f_187_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_187_, 0, v_inst_184_);
v___x_188_ = l_List_isPrefixOf___redArg(v___f_187_, v_l_u2081_185_, v_l_u2082_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object* v_inst_189_, lean_object* v_l_u2081_190_, lean_object* v_l_u2082_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_189_, v_l_u2081_190_, v_l_u2082_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_l_u2081_196_, lean_object* v_l_u2082_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_195_, v_l_u2081_196_, v_l_u2082_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_l_u2081_201_, lean_object* v_l_u2082_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_List_instDecidableIsPrefixOfDecidableEq(v_00_u03b1_199_, v_inst_200_, v_l_u2081_201_, v_l_u2082_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object* v_inst_205_, lean_object* v_l_u2081_206_, lean_object* v_l_u2082_207_){
_start:
{
lean_object* v___f_208_; uint8_t v___x_209_; 
v___f_208_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_208_, 0, v_inst_205_);
v___x_209_ = l_List_isSuffixOf___redArg(v___f_208_, v_l_u2081_206_, v_l_u2082_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object* v_inst_210_, lean_object* v_l_u2081_211_, lean_object* v_l_u2082_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_210_, v_l_u2081_211_, v_l_u2082_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_l_u2081_217_, lean_object* v_l_u2082_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_216_, v_l_u2081_217_, v_l_u2082_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_l_u2081_222_, lean_object* v_l_u2082_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_List_instDecidableIsSuffixOfDecidableEq(v_00_u03b1_220_, v_inst_221_, v_l_u2081_222_, v_l_u2082_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_h__2_228_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_1(v_h__1_227_, v___x_229_);
return v___x_230_;
}
else
{
lean_object* v_head_231_; lean_object* v_tail_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_227_);
v_head_231_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_head_231_);
v_tail_232_ = lean_ctor_get(v_x_226_, 1);
lean_inc(v_tail_232_);
lean_dec_ref_known(v_x_226_, 2);
v___x_233_ = lean_apply_2(v_h__2_228_, v_head_231_, v_tail_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_234_, lean_object* v_motive_235_, lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
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
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object* v_inst_244_, lean_object* v_l_u2081_245_, lean_object* v_l_u2082_246_){
_start:
{
lean_object* v___f_247_; uint8_t v___x_248_; 
v___f_247_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_247_, 0, v_inst_244_);
v___x_248_ = l_List_isInfixOf__internal___redArg(v___f_247_, v_l_u2081_245_, v_l_u2082_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object* v_inst_249_, lean_object* v_l_u2081_250_, lean_object* v_l_u2082_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_249_, v_l_u2081_250_, v_l_u2082_251_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_l_u2081_256_, lean_object* v_l_u2082_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_255_, v_l_u2081_256_, v_l_u2082_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_l_u2081_261_, lean_object* v_l_u2082_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_List_instDecidableIsInfixOfDecidableEq(v_00_u03b1_259_, v_inst_260_, v_l_u2081_261_, v_l_u2082_262_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
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
