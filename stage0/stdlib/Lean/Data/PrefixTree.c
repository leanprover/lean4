// Lean compiler output
// Module: Lean.Data.PrefixTree
// Imports: public import Std.Data.TreeMap.Raw.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedPrefixTreeNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedPrefixTreeNode___closed__0 = (const lean_object*)&l_Lean_instInhabitedPrefixTreeNode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_cmp_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___closed__0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___boxed(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b2_9_, lean_object* v_cmp_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_instInhabitedPrefixTreeNode(v_00_u03b1_8_, v_00_u03b2_9_, v_cmp_10_);
lean_dec_ref(v_cmp_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_cmp_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___closed__0));
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___boxed(lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_cmp_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_PrefixTreeNode_empty(v_00_u03b1_16_, v_00_u03b2_17_, v_cmp_18_);
lean_dec_ref(v_cmp_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object* v_cmp_20_, lean_object* v_val_21_, lean_object* v_k_22_){
_start:
{
if (lean_obj_tag(v_k_22_) == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec_ref(v_cmp_20_);
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v_val_21_);
v___x_24_ = lean_box(1);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_23_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_38_; 
v_head_26_ = lean_ctor_get(v_k_22_, 0);
v_tail_27_ = lean_ctor_get(v_k_22_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v_k_22_);
if (v_isSharedCheck_38_ == 0)
{
v___x_29_ = v_k_22_;
v_isShared_30_ = v_isSharedCheck_38_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_tail_27_);
lean_inc(v_head_26_);
lean_dec(v_k_22_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_38_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v_t_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
lean_inc_ref(v_cmp_20_);
v_t_31_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_20_, v_val_21_, v_tail_27_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_box(1);
v___x_34_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_20_, v_head_26_, v_t_31_, v___x_33_);
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 0);
lean_ctor_set(v___x_29_, 1, v___x_34_);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_36_ = v___x_29_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_cmp_41_, lean_object* v_val_42_, lean_object* v_k_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_41_, v_val_42_, v_k_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(lean_object* v_cmp_45_, lean_object* v_val_46_, lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
lean_dec_ref(v_cmp_45_);
v_a_49_ = lean_ctor_get(v_x_47_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_x_47_, 0);
lean_dec(v_unused_58_);
v___x_51_ = v_x_47_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v_x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_val_46_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_53_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_a_49_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
else
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_76_; 
v_a_59_ = lean_ctor_get(v_x_47_, 0);
v_a_60_ = lean_ctor_get(v_x_47_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_76_ == 0)
{
v___x_62_ = v_x_47_;
v_isShared_63_ = v_isSharedCheck_76_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_inc(v_a_59_);
lean_dec(v_x_47_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_76_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___y_67_; lean_object* v___x_72_; 
v_head_64_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_x_48_, 1);
lean_inc(v_tail_65_);
lean_dec_ref(v_x_48_);
lean_inc(v_head_64_);
lean_inc(v_a_60_);
lean_inc_ref(v_cmp_45_);
v___x_72_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_45_, v_a_60_, v_head_64_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v___x_73_; 
lean_inc_ref(v_cmp_45_);
v___x_73_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_45_, v_val_46_, v_tail_65_);
v___y_67_ = v___x_73_;
goto v___jp_66_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; 
v_val_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v___x_72_);
lean_inc_ref(v_cmp_45_);
v___x_75_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_45_, v_val_46_, v_val_74_, v_tail_65_);
v___y_67_ = v___x_75_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_45_, v_head_64_, v___y_67_, v_a_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_68_);
v___x_70_ = v___x_62_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_59_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_, lean_object* v_val_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_79_, v_val_80_, v_x_81_, v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object* v_cmp_84_, lean_object* v_t_85_, lean_object* v_k_86_, lean_object* v_val_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_84_, v_val_87_, v_t_85_, v_k_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_, lean_object* v_t_92_, lean_object* v_k_93_, lean_object* v_val_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_91_, v_val_94_, v_t_92_, v_k_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object* v_cmp_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v_a_99_; 
lean_dec_ref(v_cmp_96_);
v_a_99_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v_x_97_);
return v_a_99_;
}
else
{
lean_object* v_a_100_; lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_103_; 
v_a_100_ = lean_ctor_get(v_x_97_, 1);
lean_inc(v_a_100_);
lean_dec_ref(v_x_97_);
v_head_101_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_101_);
v_tail_102_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_tail_102_);
lean_dec_ref(v_x_98_);
lean_inc_ref(v_cmp_96_);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_96_, v_a_100_, v_head_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_104_; 
lean_dec(v_tail_102_);
lean_dec_ref(v_cmp_96_);
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v___x_103_);
v_x_97_ = v_val_105_;
v_x_98_ = v_tail_102_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_109_, v_x_110_, v_x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object* v_cmp_113_, lean_object* v_t_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_113_, v_t_114_, v_k_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_, lean_object* v_t_120_, lean_object* v_k_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_119_, v_t_120_, v_k_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object* v_cmp_123_, lean_object* v_acc_x3f_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v_a_127_; 
lean_dec_ref(v_cmp_123_);
v_a_127_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v_x_125_);
if (lean_obj_tag(v_a_127_) == 0)
{
return v_acc_x3f_124_;
}
else
{
lean_dec(v_acc_x3f_124_);
return v_a_127_;
}
}
else
{
lean_object* v_a_128_; lean_object* v_a_129_; lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; 
v_a_128_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_a_128_);
v_a_129_ = lean_ctor_get(v_x_125_, 1);
lean_inc(v_a_129_);
lean_dec_ref(v_x_125_);
v_head_130_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_x_126_, 1);
lean_inc(v_tail_131_);
lean_dec_ref(v_x_126_);
lean_inc_ref(v_cmp_123_);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_123_, v_a_129_, v_head_130_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_dec(v_tail_131_);
lean_dec(v_acc_x3f_124_);
lean_dec_ref(v_cmp_123_);
return v_a_128_;
}
else
{
if (lean_obj_tag(v_a_128_) == 0)
{
lean_object* v_val_133_; 
v_val_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_133_);
lean_dec_ref(v___x_132_);
v_x_125_ = v_val_133_;
v_x_126_ = v_tail_131_;
goto _start;
}
else
{
lean_object* v_val_135_; 
lean_dec(v_acc_x3f_124_);
v_val_135_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_132_);
v_acc_x3f_124_ = v_a_128_;
v_x_125_ = v_val_135_;
v_x_126_ = v_tail_131_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_cmp_139_, lean_object* v_acc_x3f_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_139_, v_acc_x3f_140_, v_x_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object* v_cmp_144_, lean_object* v_t_145_, lean_object* v_k_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_144_, v___x_147_, v_t_145_, v_k_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_cmp_151_, lean_object* v_t_152_, lean_object* v_k_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_box(0);
v___x_155_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_151_, v___x_154_, v_t_152_, v_k_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object* v_inst_156_, lean_object* v___f_157_, lean_object* v_a_158_, lean_object* v_d_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_156_, v___f_157_, v_d_159_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object* v_inst_161_, lean_object* v_f_162_, lean_object* v_d_163_, lean_object* v_x_164_, lean_object* v_t_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(v_inst_161_, v_f_162_, v_d_163_, v_x_164_, v_t_165_);
lean_dec(v_x_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object* v_inst_167_, lean_object* v_f_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_toApplicative_171_; lean_object* v_toBind_172_; lean_object* v_toPure_173_; lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___f_176_; 
v_toApplicative_171_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_172_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_172_);
v_toPure_173_ = lean_ctor_get(v_toApplicative_171_, 1);
v_a_174_ = lean_ctor_get(v_a_169_, 0);
lean_inc(v_a_174_);
v_a_175_ = lean_ctor_get(v_a_169_, 1);
lean_inc(v_a_175_);
lean_dec_ref(v_a_169_);
lean_inc(v_f_168_);
lean_inc_ref(v_inst_167_);
v___f_176_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_176_, 0, v_inst_167_);
lean_closure_set(v___f_176_, 1, v_f_168_);
if (lean_obj_tag(v_a_174_) == 0)
{
lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc(v_toPure_173_);
lean_dec(v_f_168_);
v___f_177_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_177_, 0, v_inst_167_);
lean_closure_set(v___f_177_, 1, v___f_176_);
lean_closure_set(v___f_177_, 2, v_a_175_);
v___x_178_ = lean_apply_2(v_toPure_173_, lean_box(0), v_a_170_);
v___x_179_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_178_, v___f_177_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_val_180_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v_a_174_);
v___f_181_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_181_, 0, v_inst_167_);
lean_closure_set(v___f_181_, 1, v___f_176_);
lean_closure_set(v___f_181_, 2, v_a_175_);
v___x_182_ = lean_apply_2(v_f_168_, v_val_180_, v_a_170_);
v___x_183_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_182_, v___f_181_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object* v_inst_184_, lean_object* v_f_185_, lean_object* v_d_186_, lean_object* v_x_187_, lean_object* v_t_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_184_, v_f_185_, v_t_188_, v_d_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(lean_object* v_m_190_, lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_00_u03c3_193_, lean_object* v_inst_194_, lean_object* v_cmp_195_, lean_object* v_f_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_194_, v_f_196_, v_a_197_, v_a_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___boxed(lean_object* v_m_200_, lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_00_u03c3_203_, lean_object* v_inst_204_, lean_object* v_cmp_205_, lean_object* v_f_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(v_m_200_, v_00_u03b1_201_, v_00_u03b2_202_, v_00_u03c3_203_, v_inst_204_, v_cmp_205_, v_f_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_cmp_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object* v_inst_210_, lean_object* v_cmp_211_, lean_object* v_init_212_, lean_object* v_f_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
if (lean_obj_tag(v_a_214_) == 0)
{
lean_object* v___x_217_; 
lean_dec(v_init_212_);
lean_dec_ref(v_cmp_211_);
v___x_217_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_210_, v_f_213_, v_a_215_, v_a_216_);
return v___x_217_;
}
else
{
lean_object* v_toApplicative_218_; lean_object* v_toPure_219_; lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v_a_222_; lean_object* v___x_223_; 
v_toApplicative_218_ = lean_ctor_get(v_inst_210_, 0);
v_toPure_219_ = lean_ctor_get(v_toApplicative_218_, 1);
v_head_220_ = lean_ctor_get(v_a_214_, 0);
lean_inc(v_head_220_);
v_tail_221_ = lean_ctor_get(v_a_214_, 1);
lean_inc(v_tail_221_);
lean_dec_ref(v_a_214_);
v_a_222_ = lean_ctor_get(v_a_215_, 1);
lean_inc(v_a_222_);
lean_dec_ref(v_a_215_);
lean_inc_ref(v_cmp_211_);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_211_, v_a_222_, v_head_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
lean_inc(v_toPure_219_);
lean_dec(v_tail_221_);
lean_dec(v_a_216_);
lean_dec(v_f_213_);
lean_dec_ref(v_cmp_211_);
lean_dec_ref(v_inst_210_);
v___x_224_ = lean_apply_2(v_toPure_219_, lean_box(0), v_init_212_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v___x_223_);
v_a_214_ = v_tail_221_;
v_a_215_ = v_val_225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_object* v_m_227_, lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_00_u03c3_230_, lean_object* v_inst_231_, lean_object* v_cmp_232_, lean_object* v_init_233_, lean_object* v_f_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_231_, v_cmp_232_, v_init_233_, v_f_234_, v_a_235_, v_a_236_, v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object* v_inst_239_, lean_object* v_cmp_240_, lean_object* v_t_241_, lean_object* v_k_242_, lean_object* v_init_243_, lean_object* v_f_244_){
_start:
{
lean_object* v___x_245_; 
lean_inc(v_init_243_);
v___x_245_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_239_, v_cmp_240_, v_init_243_, v_f_244_, v_k_242_, v_t_241_, v_init_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object* v_m_246_, lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_00_u03c3_249_, lean_object* v_inst_250_, lean_object* v_cmp_251_, lean_object* v_t_252_, lean_object* v_k_253_, lean_object* v_init_254_, lean_object* v_f_255_){
_start:
{
lean_object* v___x_256_; 
lean_inc(v_init_254_);
v___x_256_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_250_, v_cmp_251_, v_init_254_, v_f_255_, v_k_253_, v_t_252_, v_init_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg(lean_object* v_p_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg___boxed(lean_object* v_p_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_PrefixTree_empty___redArg(v_p_259_);
lean_dec_ref(v_p_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_p_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object* v_00_u03b1_265_, lean_object* v_00_u03b2_266_, lean_object* v_p_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_PrefixTree_empty(v_00_u03b1_265_, v_00_u03b2_266_, v_p_267_);
lean_dec_ref(v_p_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg(lean_object* v_p_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg___boxed(lean_object* v_p_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_instInhabitedPrefixTree___redArg(v_p_271_);
lean_dec_ref(v_p_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_p_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_p_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_instInhabitedPrefixTree(v_00_u03b1_277_, v_00_u03b2_278_, v_p_279_);
lean_dec_ref(v_p_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg(lean_object* v_p_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(lean_object* v_p_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_instEmptyCollectionPrefixTree___redArg(v_p_283_);
lean_dec_ref(v_p_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_p_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_p_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_instEmptyCollectionPrefixTree(v_00_u03b1_289_, v_00_u03b2_290_, v_p_291_);
lean_dec_ref(v_p_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object* v_p_293_, lean_object* v_t_294_, lean_object* v_k_295_, lean_object* v_v_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_293_, v_v_296_, v_t_294_, v_k_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_p_300_, lean_object* v_t_301_, lean_object* v_k_302_, lean_object* v_v_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_300_, v_v_303_, v_t_301_, v_k_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object* v_p_305_, lean_object* v_t_306_, lean_object* v_k_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_305_, v_t_306_, v_k_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object* v_00_u03b1_309_, lean_object* v_00_u03b2_310_, lean_object* v_p_311_, lean_object* v_t_312_, lean_object* v_k_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_311_, v_t_312_, v_k_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object* v_p_315_, lean_object* v_t_316_, lean_object* v_k_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_box(0);
v___x_319_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_315_, v___x_318_, v_t_316_, v_k_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_p_322_, lean_object* v_t_323_, lean_object* v_k_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box(0);
v___x_326_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_322_, v___x_325_, v_t_323_, v_k_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object* v_p_327_, lean_object* v_inst_328_, lean_object* v_t_329_, lean_object* v_k_330_, lean_object* v_init_331_, lean_object* v_f_332_){
_start:
{
lean_object* v___x_333_; 
lean_inc(v_init_331_);
v___x_333_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_328_, v_p_327_, v_init_331_, v_f_332_, v_k_330_, v_t_329_, v_init_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object* v_m_334_, lean_object* v_00_u03b1_335_, lean_object* v_00_u03b2_336_, lean_object* v_p_337_, lean_object* v_00_u03c3_338_, lean_object* v_inst_339_, lean_object* v_t_340_, lean_object* v_k_341_, lean_object* v_init_342_, lean_object* v_f_343_){
_start:
{
lean_object* v___x_344_; 
lean_inc(v_init_342_);
v___x_344_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_339_, v_p_337_, v_init_342_, v_f_343_, v_k_341_, v_t_340_, v_init_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object* v_p_345_, lean_object* v_inst_346_, lean_object* v_t_347_, lean_object* v_init_348_, lean_object* v_f_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
lean_inc(v_init_348_);
v___x_351_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_346_, v_p_345_, v_init_348_, v_f_349_, v___x_350_, v_t_347_, v_init_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object* v_m_352_, lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_p_355_, lean_object* v_00_u03c3_356_, lean_object* v_inst_357_, lean_object* v_t_358_, lean_object* v_init_359_, lean_object* v_f_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(0);
lean_inc(v_init_359_);
v___x_362_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_357_, v_p_355_, v_init_359_, v_f_360_, v___x_361_, v_t_358_, v_init_359_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object* v_f_363_, lean_object* v_b_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_1(v_f_363_, v_b_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object* v_p_367_, lean_object* v_inst_368_, lean_object* v_t_369_, lean_object* v_k_370_, lean_object* v_f_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___f_372_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_372_, 0, v_f_371_);
v___x_373_ = lean_box(0);
v___x_374_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_368_, v_p_367_, v___x_373_, v___f_372_, v_k_370_, v_t_369_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object* v_m_375_, lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_p_378_, lean_object* v_inst_379_, lean_object* v_t_380_, lean_object* v_k_381_, lean_object* v_f_382_){
_start:
{
lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___f_383_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_383_, 0, v_f_382_);
v___x_384_ = lean_box(0);
v___x_385_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_379_, v_p_378_, v___x_384_, v___f_383_, v_k_381_, v_t_380_, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object* v_p_386_, lean_object* v_inst_387_, lean_object* v_t_388_, lean_object* v_f_389_){
_start:
{
lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___f_390_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_390_, 0, v_f_389_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_box(0);
v___x_393_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_387_, v_p_386_, v___x_392_, v___f_390_, v___x_391_, v_t_388_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object* v_m_394_, lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_p_397_, lean_object* v_inst_398_, lean_object* v_t_399_, lean_object* v_f_400_){
_start:
{
lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___f_401_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_401_, 0, v_f_400_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_box(0);
v___x_404_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_398_, v_p_397_, v___x_403_, v___f_401_, v___x_402_, v_t_399_, v___x_403_);
return v___x_404_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PrefixTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_PrefixTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PrefixTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PrefixTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_PrefixTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_PrefixTree(builtin);
}
#ifdef __cplusplus
}
#endif
