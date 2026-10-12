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
lean_object* l_List_instTransSubsetMem___redArg(){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
LEAN_EXPORT void l_List_instTransSubsetMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_29_;
v_res_29_ = l_List_instTransSubsetMem___redArg();
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem___redArg___boxed(lean_object* v___dummy_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_List_instTransSubsetMem___redArg();
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object* v_00_u03b1_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
lean_object* l_List_instTransSubset___redArg(){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT void l_List_instTransSubset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_36_;
v_res_36_ = l_List_instTransSubset___redArg();
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_List_instTransSubset___redArg___boxed(lean_object* v___dummy_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_List_instTransSubset___redArg();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object* v_00_u03b1_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
lean_object* l_List_instTransSublist___redArg(){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT void l_List_instTransSublist___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_43_;
v_res_43_ = l_List_instTransSublist___redArg();
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_List_instTransSublist___redArg___boxed(lean_object* v___dummy_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_List_instTransSublist___redArg();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object* v_00_u03b1_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
lean_object* l_List_instTransSublistSubset___redArg(){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
LEAN_EXPORT void l_List_instTransSublistSubset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_50_;
v_res_50_ = l_List_instTransSublistSubset___redArg();
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset___redArg___boxed(lean_object* v___dummy_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_List_instTransSublistSubset___redArg();
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object* v_00_u03b1_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_box(0);
return v___x_54_;
}
}
lean_object* l_List_instTransSubsetSublist___redArg(){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT void l_List_instTransSubsetSublist___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_57_;
v_res_57_ = l_List_instTransSubsetSublist___redArg();
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_List_instTransSubsetSublist___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object* v_00_u03b1_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
lean_object* l_List_instTransSublistMem___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT void l_List_instTransSublistMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_64_;
v_res_64_ = l_List_instTransSublistMem___redArg();
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_List_instTransSublistMem___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object* v_00_u03b1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_70_);
v_val_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v_x_69_, 1);
v___x_75_ = lean_apply_1(v_h__2_71_, v_val_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_76_, lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_80_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__1_79_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_79_);
v_val_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v_x_78_, 1);
v___x_84_ = lean_apply_1(v_h__2_80_, v_val_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_, lean_object* v_h__3_89_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_90_; 
lean_dec(v_h__3_89_);
lean_dec(v_h__2_88_);
v___x_90_ = lean_apply_1(v_h__1_87_, v_x_86_);
return v___x_90_;
}
else
{
lean_dec(v_h__1_87_);
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_91_; 
lean_dec(v_h__3_89_);
v___x_91_ = lean_apply_2(v_h__2_88_, v_x_85_, lean_box(0));
return v___x_91_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_88_);
v_head_92_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_tail_93_);
lean_dec_ref_known(v_x_85_, 2);
v_head_94_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_head_94_);
v_tail_95_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_tail_95_);
lean_dec_ref_known(v_x_86_, 2);
v___x_96_ = lean_apply_4(v_h__3_89_, v_head_92_, v_tail_93_, v_head_94_, v_tail_95_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(lean_object* v_00_u03b1_97_, lean_object* v_motive_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v___x_104_; 
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v___x_104_ = lean_apply_1(v_h__1_101_, v_x_100_);
return v___x_104_;
}
else
{
lean_dec(v_h__1_101_);
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_105_; 
lean_dec(v_h__3_103_);
v___x_105_ = lean_apply_2(v_h__2_102_, v_x_99_, lean_box(0));
return v___x_105_;
}
else
{
lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_102_);
v_head_106_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_tail_107_);
lean_dec_ref_known(v_x_99_, 2);
v_head_108_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_head_108_);
v_tail_109_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_tail_109_);
lean_dec_ref_known(v_x_100_, 2);
v___x_110_ = lean_apply_4(v_h__3_103_, v_head_106_, v_tail_107_, v_head_108_, v_tail_109_);
return v___x_110_;
}
}
}
}
uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object* v_inst_111_, lean_object* v_l_u2081_112_, lean_object* v_l_u2082_113_){
_start:
{
lean_object* v___f_114_; uint8_t v___x_115_; 
v___f_114_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_114_, 0, v_inst_111_);
v___x_115_ = l_List_isSublist___redArg(v___f_114_, v_l_u2081_112_, v_l_u2082_113_);
return v___x_115_;
}
}
LEAN_EXPORT void l_List_instDecidableSublistOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_111_ = stack[0].m_obj;
lean_object* v_l_u2081_112_ = stack[1].m_obj;
lean_object* v_l_u2082_113_ = stack[2].m_obj;
uint8_t v_res_116_;
v_res_116_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_111_, v_l_u2081_112_, v_l_u2082_113_);
stack->m_num = v_res_116_;
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object* v_inst_117_, lean_object* v_l_u2081_118_, lean_object* v_l_u2082_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_117_, v_l_u2081_118_, v_l_u2082_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_l_u2081_124_, lean_object* v_l_u2082_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = l_List_instDecidableSublistOfDecidableEq___redArg(v_inst_123_, v_l_u2081_124_, v_l_u2082_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_List_instDecidableSublistOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_123_ = stack[1].m_obj;
lean_object* v_l_u2081_124_ = stack[2].m_obj;
lean_object* v_l_u2082_125_ = stack[3].m_obj;
uint8_t v_res_127_;
v_res_127_ = l_List_instDecidableSublistOfDecidableEq(lean_box(0), v_inst_123_, v_l_u2081_124_, v_l_u2082_125_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_l_u2081_130_, lean_object* v_l_u2082_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_List_instDecidableSublistOfDecidableEq(v_00_u03b1_128_, v_inst_129_, v_l_u2081_130_, v_l_u2082_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_, lean_object* v_h__3_137_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__3_137_);
lean_dec(v_h__2_136_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__1_135_, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_tail_140_; 
lean_dec(v_h__1_135_);
v_tail_140_ = lean_ctor_get(v_x_134_, 1);
if (lean_obj_tag(v_tail_140_) == 0)
{
lean_object* v_head_141_; lean_object* v___x_142_; 
lean_dec(v_h__3_137_);
v_head_141_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_head_141_);
lean_dec_ref_known(v_x_134_, 2);
v___x_142_ = lean_apply_1(v_h__2_136_, v_head_141_);
return v___x_142_;
}
else
{
lean_object* v_head_143_; lean_object* v___x_144_; 
lean_inc(v_tail_140_);
lean_dec(v_h__2_136_);
v_head_143_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_head_143_);
lean_dec_ref_known(v_x_134_, 2);
v___x_144_ = lean_apply_3(v_h__3_137_, v_head_143_, v_tail_140_, lean_box(0));
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sublist_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_145_, lean_object* v_motive_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_h__3_150_);
lean_dec(v_h__2_149_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v_h__1_148_, v___x_151_);
return v___x_152_;
}
else
{
lean_object* v_tail_153_; 
lean_dec(v_h__1_148_);
v_tail_153_ = lean_ctor_get(v_x_147_, 1);
if (lean_obj_tag(v_tail_153_) == 0)
{
lean_object* v_head_154_; lean_object* v___x_155_; 
lean_dec(v_h__3_150_);
v_head_154_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_head_154_);
lean_dec_ref_known(v_x_147_, 2);
v___x_155_ = lean_apply_1(v_h__2_149_, v_head_154_);
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v___x_157_; 
lean_inc(v_tail_153_);
lean_dec(v_h__2_149_);
v_head_156_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_head_156_);
lean_dec_ref_known(v_x_147_, 2);
v___x_157_ = lean_apply_3(v_h__3_150_, v_head_156_, v_tail_153_, lean_box(0));
return v___x_157_;
}
}
}
}
uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object* v_inst_158_, lean_object* v_l_u2081_159_, lean_object* v_l_u2082_160_){
_start:
{
lean_object* v___f_161_; uint8_t v___x_162_; 
v___f_161_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_161_, 0, v_inst_158_);
v___x_162_ = l_List_isPrefixOf___redArg(v___f_161_, v_l_u2081_159_, v_l_u2082_160_);
return v___x_162_;
}
}
LEAN_EXPORT void l_List_instDecidableIsPrefixOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_158_ = stack[0].m_obj;
lean_object* v_l_u2081_159_ = stack[1].m_obj;
lean_object* v_l_u2082_160_ = stack[2].m_obj;
uint8_t v_res_163_;
v_res_163_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_158_, v_l_u2081_159_, v_l_u2082_160_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object* v_inst_164_, lean_object* v_l_u2081_165_, lean_object* v_l_u2082_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_164_, v_l_u2081_165_, v_l_u2082_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_l_u2081_171_, lean_object* v_l_u2082_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(v_inst_170_, v_l_u2081_171_, v_l_u2082_172_);
return v___x_173_;
}
}
LEAN_EXPORT void l_List_instDecidableIsPrefixOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_170_ = stack[1].m_obj;
lean_object* v_l_u2081_171_ = stack[2].m_obj;
lean_object* v_l_u2082_172_ = stack[3].m_obj;
uint8_t v_res_174_;
v_res_174_ = l_List_instDecidableIsPrefixOfDecidableEq(lean_box(0), v_inst_170_, v_l_u2081_171_, v_l_u2082_172_);
stack->m_num = v_res_174_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_l_u2081_177_, lean_object* v_l_u2082_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_List_instDecidableIsPrefixOfDecidableEq(v_00_u03b1_175_, v_inst_176_, v_l_u2081_177_, v_l_u2082_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object* v_inst_181_, lean_object* v_l_u2081_182_, lean_object* v_l_u2082_183_){
_start:
{
lean_object* v___f_184_; uint8_t v___x_185_; 
v___f_184_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_184_, 0, v_inst_181_);
v___x_185_ = l_List_isSuffixOf___redArg(v___f_184_, v_l_u2081_182_, v_l_u2082_183_);
return v___x_185_;
}
}
LEAN_EXPORT void l_List_instDecidableIsSuffixOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_181_ = stack[0].m_obj;
lean_object* v_l_u2081_182_ = stack[1].m_obj;
lean_object* v_l_u2082_183_ = stack[2].m_obj;
uint8_t v_res_186_;
v_res_186_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_181_, v_l_u2081_182_, v_l_u2082_183_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object* v_inst_187_, lean_object* v_l_u2081_188_, lean_object* v_l_u2082_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_187_, v_l_u2081_188_, v_l_u2082_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_, lean_object* v_l_u2081_194_, lean_object* v_l_u2082_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(v_inst_193_, v_l_u2081_194_, v_l_u2082_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_List_instDecidableIsSuffixOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_193_ = stack[1].m_obj;
lean_object* v_l_u2081_194_ = stack[2].m_obj;
lean_object* v_l_u2082_195_ = stack[3].m_obj;
uint8_t v_res_197_;
v_res_197_ = l_List_instDecidableIsSuffixOfDecidableEq(lean_box(0), v_inst_193_, v_l_u2081_194_, v_l_u2082_195_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_l_u2081_200_, lean_object* v_l_u2082_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_List_instDecidableIsSuffixOfDecidableEq(v_00_u03b1_198_, v_inst_199_, v_l_u2081_200_, v_l_u2082_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
uint8_t l_List_instDecidableIsInfixOfDecidableEq___redArg(lean_object* v_inst_204_, lean_object* v_l_u2081_205_, lean_object* v_l_u2082_206_){
_start:
{
lean_object* v___f_207_; uint8_t v___x_208_; 
v___f_207_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_207_, 0, v_inst_204_);
v___x_208_ = l_List_isInfixOf__internal___redArg(v___f_207_, v_l_u2081_205_, v_l_u2082_206_);
return v___x_208_;
}
}
LEAN_EXPORT void l_List_instDecidableIsInfixOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_204_ = stack[0].m_obj;
lean_object* v_l_u2081_205_ = stack[1].m_obj;
lean_object* v_l_u2082_206_ = stack[2].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_204_, v_l_u2081_205_, v_l_u2082_206_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(lean_object* v_inst_210_, lean_object* v_l_u2081_211_, lean_object* v_l_u2082_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_210_, v_l_u2081_211_, v_l_u2082_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
uint8_t l_List_instDecidableIsInfixOfDecidableEq(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_l_u2081_217_, lean_object* v_l_u2082_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(v_inst_216_, v_l_u2081_217_, v_l_u2082_218_);
return v___x_219_;
}
}
LEAN_EXPORT void l_List_instDecidableIsInfixOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_216_ = stack[1].m_obj;
lean_object* v_l_u2081_217_ = stack[2].m_obj;
lean_object* v_l_u2082_218_ = stack[3].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_List_instDecidableIsInfixOfDecidableEq(lean_box(0), v_inst_216_, v_l_u2081_217_, v_l_u2082_218_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_List_instDecidableIsInfixOfDecidableEq___boxed(lean_object* v_00_u03b1_221_, lean_object* v_inst_222_, lean_object* v_l_u2081_223_, lean_object* v_l_u2082_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_List_instDecidableIsInfixOfDecidableEq(v_00_u03b1_221_, v_inst_222_, v_l_u2081_223_, v_l_u2082_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
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
