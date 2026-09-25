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
static const lean_ctor_object l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPrefixTreeNode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPrefixTreeNode___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PrefixTreeNode_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrefixTreeNode_empty___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg();
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0));
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_instInhabitedPrefixTreeNode___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_instInhabitedPrefixTreeNode___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_instInhabitedPrefixTreeNode___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_cmp_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_instInhabitedPrefixTreeNode___closed__0, &l_Lean_instInhabitedPrefixTreeNode___closed__0_once, _init_l_Lean_instInhabitedPrefixTreeNode___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_cmp_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_instInhabitedPrefixTreeNode(v_00_u03b1_13_, v_00_u03b2_14_, v_cmp_15_);
lean_dec_ref(v_cmp_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___redArg(){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___redArg___boxed(lean_object* v___dummy_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_PrefixTreeNode_empty___redArg();
return v_res_20_;
}
}
static lean_object* _init_l_Lean_PrefixTreeNode_empty___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PrefixTreeNode_empty___redArg();
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_cmp_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___boxed(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_cmp_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_PrefixTreeNode_empty(v_00_u03b1_26_, v_00_u03b2_27_, v_cmp_28_);
lean_dec_ref(v_cmp_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object* v_cmp_30_, lean_object* v_val_31_, lean_object* v_k_32_){
_start:
{
if (lean_obj_tag(v_k_32_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec_ref(v_cmp_30_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_val_31_);
v___x_34_ = lean_box(1);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_33_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_head_36_; lean_object* v_tail_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_48_; 
v_head_36_ = lean_ctor_get(v_k_32_, 0);
v_tail_37_ = lean_ctor_get(v_k_32_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_k_32_);
if (v_isSharedCheck_48_ == 0)
{
v___x_39_ = v_k_32_;
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_tail_37_);
lean_inc(v_head_36_);
lean_dec(v_k_32_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_t_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
lean_inc_ref(v_cmp_30_);
v_t_41_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_30_, v_val_31_, v_tail_37_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_box(1);
v___x_44_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_30_, v_head_36_, v_t_41_, v___x_43_);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 0);
lean_ctor_set(v___x_39_, 1, v___x_44_);
lean_ctor_set(v___x_39_, 0, v___x_42_);
v___x_46_ = v___x_39_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_cmp_51_, lean_object* v_val_52_, lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_51_, v_val_52_, v_k_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(lean_object* v_cmp_55_, lean_object* v_val_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref(v_cmp_55_);
v_a_59_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v_x_57_, 0);
lean_dec(v_unused_68_);
v___x_61_ = v_x_57_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v_x_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_val_56_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_a_59_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
else
{
lean_object* v_a_69_; lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_86_; 
v_a_69_ = lean_ctor_get(v_x_57_, 0);
v_a_70_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_86_ == 0)
{
v___x_72_ = v_x_57_;
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_inc(v_a_69_);
lean_dec(v_x_57_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___y_77_; lean_object* v___x_82_; 
v_head_74_ = lean_ctor_get(v_x_58_, 0);
lean_inc_n(v_head_74_, 2);
v_tail_75_ = lean_ctor_get(v_x_58_, 1);
lean_inc(v_tail_75_);
lean_dec_ref_known(v_x_58_, 2);
lean_inc(v_a_70_);
lean_inc_ref(v_cmp_55_);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_55_, v_a_70_, v_head_74_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; 
lean_inc_ref(v_cmp_55_);
v___x_83_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_55_, v_val_56_, v_tail_75_);
v___y_77_ = v___x_83_;
goto v___jp_76_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
v_val_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v___x_82_, 1);
lean_inc_ref(v_cmp_55_);
v___x_85_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_55_, v_val_56_, v_val_84_, v_tail_75_);
v___y_77_ = v___x_85_;
goto v___jp_76_;
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_55_, v_head_74_, v___y_77_, v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_78_);
v___x_80_ = v___x_72_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_, lean_object* v_val_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_89_, v_val_90_, v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object* v_cmp_94_, lean_object* v_t_95_, lean_object* v_k_96_, lean_object* v_val_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_94_, v_val_97_, v_t_95_, v_k_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_cmp_101_, lean_object* v_t_102_, lean_object* v_k_103_, lean_object* v_val_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_101_, v_val_104_, v_t_102_, v_k_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object* v_cmp_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_a_109_; 
lean_dec_ref(v_cmp_106_);
v_a_109_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v_x_107_);
return v_a_109_;
}
else
{
lean_object* v_a_110_; lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_113_; 
v_a_110_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_a_110_);
lean_dec_ref(v_x_107_);
v_head_111_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_111_);
v_tail_112_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_tail_112_);
lean_dec_ref_known(v_x_108_, 2);
lean_inc_ref(v_cmp_106_);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_106_, v_a_110_, v_head_111_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v___x_114_; 
lean_dec(v_tail_112_);
lean_dec_ref(v_cmp_106_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v_val_115_; 
v_val_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v___x_113_, 1);
v_x_107_ = v_val_115_;
v_x_108_ = v_tail_112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_119_, v_x_120_, v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object* v_cmp_123_, lean_object* v_t_124_, lean_object* v_k_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_123_, v_t_124_, v_k_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_cmp_129_, lean_object* v_t_130_, lean_object* v_k_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_129_, v_t_130_, v_k_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object* v_cmp_133_, lean_object* v_acc_x3f_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_a_137_; 
lean_dec_ref(v_cmp_133_);
v_a_137_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_a_137_);
lean_dec_ref(v_x_135_);
if (lean_obj_tag(v_a_137_) == 0)
{
return v_acc_x3f_134_;
}
else
{
lean_dec(v_acc_x3f_134_);
return v_a_137_;
}
}
else
{
lean_object* v_a_138_; lean_object* v_a_139_; lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_142_; 
v_a_138_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_a_138_);
v_a_139_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_a_139_);
lean_dec_ref(v_x_135_);
v_head_140_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_head_140_);
v_tail_141_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_tail_141_);
lean_dec_ref_known(v_x_136_, 2);
lean_inc_ref(v_cmp_133_);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_133_, v_a_139_, v_head_140_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_dec(v_tail_141_);
lean_dec(v_acc_x3f_134_);
lean_dec_ref(v_cmp_133_);
return v_a_138_;
}
else
{
if (lean_obj_tag(v_a_138_) == 0)
{
lean_object* v_val_143_; 
v_val_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v___x_142_, 1);
v_x_135_ = v_val_143_;
v_x_136_ = v_tail_141_;
goto _start;
}
else
{
lean_object* v_val_145_; 
lean_dec(v_acc_x3f_134_);
v_val_145_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v___x_142_, 1);
v_acc_x3f_134_ = v_a_138_;
v_x_135_ = v_val_145_;
v_x_136_ = v_tail_141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_cmp_149_, lean_object* v_acc_x3f_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_149_, v_acc_x3f_150_, v_x_151_, v_x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object* v_cmp_154_, lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(0);
v___x_158_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_154_, v___x_157_, v_t_155_, v_k_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_cmp_161_, lean_object* v_t_162_, lean_object* v_k_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_box(0);
v___x_165_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_161_, v___x_164_, v_t_162_, v_k_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object* v_inst_166_, lean_object* v___f_167_, lean_object* v_a_168_, lean_object* v_d_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_166_, v___f_167_, v_d_169_, v_a_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object* v_inst_171_, lean_object* v_f_172_, lean_object* v_d_173_, lean_object* v_x_174_, lean_object* v_t_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(v_inst_171_, v_f_172_, v_d_173_, v_x_174_, v_t_175_);
lean_dec(v_x_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object* v_inst_177_, lean_object* v_f_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___f_186_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_177_, 0);
v_toBind_182_ = lean_ctor_get(v_inst_177_, 1);
lean_inc(v_toBind_182_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
v_a_184_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_a_184_);
v_a_185_ = lean_ctor_get(v_a_179_, 1);
lean_inc(v_a_185_);
lean_dec_ref(v_a_179_);
lean_inc(v_f_178_);
lean_inc_ref(v_inst_177_);
v___f_186_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_186_, 0, v_inst_177_);
lean_closure_set(v___f_186_, 1, v_f_178_);
if (lean_obj_tag(v_a_184_) == 0)
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v_toPure_183_);
lean_dec(v_f_178_);
v___f_187_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_187_, 0, v_inst_177_);
lean_closure_set(v___f_187_, 1, v___f_186_);
lean_closure_set(v___f_187_, 2, v_a_185_);
v___x_188_ = lean_apply_2(v_toPure_183_, lean_box(0), v_a_180_);
v___x_189_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_188_, v___f_187_);
return v___x_189_;
}
else
{
lean_object* v_val_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_val_190_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_a_184_, 1);
v___f_191_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_191_, 0, v_inst_177_);
lean_closure_set(v___f_191_, 1, v___f_186_);
lean_closure_set(v___f_191_, 2, v_a_185_);
v___x_192_ = lean_apply_2(v_f_178_, v_val_190_, v_a_180_);
v___x_193_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_192_, v___f_191_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object* v_inst_194_, lean_object* v_f_195_, lean_object* v_d_196_, lean_object* v_x_197_, lean_object* v_t_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_194_, v_f_195_, v_t_198_, v_d_196_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(lean_object* v_m_200_, lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_00_u03c3_203_, lean_object* v_inst_204_, lean_object* v_cmp_205_, lean_object* v_f_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_204_, v_f_206_, v_a_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___boxed(lean_object* v_m_210_, lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_00_u03c3_213_, lean_object* v_inst_214_, lean_object* v_cmp_215_, lean_object* v_f_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(v_m_210_, v_00_u03b1_211_, v_00_u03b2_212_, v_00_u03c3_213_, v_inst_214_, v_cmp_215_, v_f_216_, v_a_217_, v_a_218_);
lean_dec_ref(v_cmp_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object* v_inst_220_, lean_object* v_cmp_221_, lean_object* v_init_222_, lean_object* v_f_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
if (lean_obj_tag(v_a_224_) == 0)
{
lean_object* v___x_227_; 
lean_dec(v_init_222_);
lean_dec_ref(v_cmp_221_);
v___x_227_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_220_, v_f_223_, v_a_225_, v_a_226_);
return v___x_227_;
}
else
{
lean_object* v_toApplicative_228_; lean_object* v_toPure_229_; lean_object* v_head_230_; lean_object* v_tail_231_; lean_object* v_a_232_; lean_object* v___x_233_; 
v_toApplicative_228_ = lean_ctor_get(v_inst_220_, 0);
v_toPure_229_ = lean_ctor_get(v_toApplicative_228_, 1);
v_head_230_ = lean_ctor_get(v_a_224_, 0);
lean_inc(v_head_230_);
v_tail_231_ = lean_ctor_get(v_a_224_, 1);
lean_inc(v_tail_231_);
lean_dec_ref_known(v_a_224_, 2);
v_a_232_ = lean_ctor_get(v_a_225_, 1);
lean_inc(v_a_232_);
lean_dec_ref(v_a_225_);
lean_inc_ref(v_cmp_221_);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_221_, v_a_232_, v_head_230_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; 
lean_inc(v_toPure_229_);
lean_dec(v_tail_231_);
lean_dec(v_a_226_);
lean_dec(v_f_223_);
lean_dec_ref(v_cmp_221_);
lean_dec_ref(v_inst_220_);
v___x_234_ = lean_apply_2(v_toPure_229_, lean_box(0), v_init_222_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; 
v_val_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_233_, 1);
v_a_224_ = v_tail_231_;
v_a_225_ = v_val_235_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_object* v_m_237_, lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_00_u03c3_240_, lean_object* v_inst_241_, lean_object* v_cmp_242_, lean_object* v_init_243_, lean_object* v_f_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_241_, v_cmp_242_, v_init_243_, v_f_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object* v_inst_249_, lean_object* v_cmp_250_, lean_object* v_t_251_, lean_object* v_k_252_, lean_object* v_init_253_, lean_object* v_f_254_){
_start:
{
lean_object* v___x_255_; 
lean_inc(v_init_253_);
v___x_255_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_249_, v_cmp_250_, v_init_253_, v_f_254_, v_k_252_, v_t_251_, v_init_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object* v_m_256_, lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_00_u03c3_259_, lean_object* v_inst_260_, lean_object* v_cmp_261_, lean_object* v_t_262_, lean_object* v_k_263_, lean_object* v_init_264_, lean_object* v_f_265_){
_start:
{
lean_object* v___x_266_; 
lean_inc(v_init_264_);
v___x_266_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_260_, v_cmp_261_, v_init_264_, v_f_265_, v_k_263_, v_t_262_, v_init_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg(){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg___boxed(lean_object* v___dummy_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PrefixTree_empty___redArg();
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_p_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_p_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PrefixTree_empty(v_00_u03b1_275_, v_00_u03b2_276_, v_p_277_);
lean_dec_ref(v_p_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg(){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg___boxed(lean_object* v___dummy_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_instInhabitedPrefixTree___redArg();
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_p_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_p_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_instInhabitedPrefixTree(v_00_u03b1_287_, v_00_u03b2_288_, v_p_289_);
lean_dec_ref(v_p_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg(){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(lean_object* v___dummy_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_instEmptyCollectionPrefixTree___redArg();
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_p_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_p_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_instEmptyCollectionPrefixTree(v_00_u03b1_299_, v_00_u03b2_300_, v_p_301_);
lean_dec_ref(v_p_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object* v_p_303_, lean_object* v_t_304_, lean_object* v_k_305_, lean_object* v_v_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_303_, v_v_306_, v_t_304_, v_k_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_p_310_, lean_object* v_t_311_, lean_object* v_k_312_, lean_object* v_v_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_310_, v_v_313_, v_t_311_, v_k_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object* v_p_315_, lean_object* v_t_316_, lean_object* v_k_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_315_, v_t_316_, v_k_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_p_321_, lean_object* v_t_322_, lean_object* v_k_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_321_, v_t_322_, v_k_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object* v_p_325_, lean_object* v_t_326_, lean_object* v_k_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_box(0);
v___x_329_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_325_, v___x_328_, v_t_326_, v_k_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_p_332_, lean_object* v_t_333_, lean_object* v_k_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
v___x_336_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_332_, v___x_335_, v_t_333_, v_k_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object* v_p_337_, lean_object* v_inst_338_, lean_object* v_t_339_, lean_object* v_k_340_, lean_object* v_init_341_, lean_object* v_f_342_){
_start:
{
lean_object* v___x_343_; 
lean_inc(v_init_341_);
v___x_343_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_338_, v_p_337_, v_init_341_, v_f_342_, v_k_340_, v_t_339_, v_init_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object* v_m_344_, lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_p_347_, lean_object* v_00_u03c3_348_, lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_k_351_, lean_object* v_init_352_, lean_object* v_f_353_){
_start:
{
lean_object* v___x_354_; 
lean_inc(v_init_352_);
v___x_354_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_349_, v_p_347_, v_init_352_, v_f_353_, v_k_351_, v_t_350_, v_init_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object* v_p_355_, lean_object* v_inst_356_, lean_object* v_t_357_, lean_object* v_init_358_, lean_object* v_f_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
lean_inc(v_init_358_);
v___x_361_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_356_, v_p_355_, v_init_358_, v_f_359_, v___x_360_, v_t_357_, v_init_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object* v_m_362_, lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_p_365_, lean_object* v_00_u03c3_366_, lean_object* v_inst_367_, lean_object* v_t_368_, lean_object* v_init_369_, lean_object* v_f_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
lean_inc(v_init_369_);
v___x_372_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_367_, v_p_365_, v_init_369_, v_f_370_, v___x_371_, v_t_368_, v_init_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object* v_f_373_, lean_object* v_b_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_apply_1(v_f_373_, v_b_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object* v_p_377_, lean_object* v_inst_378_, lean_object* v_t_379_, lean_object* v_k_380_, lean_object* v_f_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___f_382_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_382_, 0, v_f_381_);
v___x_383_ = lean_box(0);
v___x_384_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_378_, v_p_377_, v___x_383_, v___f_382_, v_k_380_, v_t_379_, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object* v_m_385_, lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_p_388_, lean_object* v_inst_389_, lean_object* v_t_390_, lean_object* v_k_391_, lean_object* v_f_392_){
_start:
{
lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___f_393_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_393_, 0, v_f_392_);
v___x_394_ = lean_box(0);
v___x_395_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_389_, v_p_388_, v___x_394_, v___f_393_, v_k_391_, v_t_390_, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object* v_p_396_, lean_object* v_inst_397_, lean_object* v_t_398_, lean_object* v_f_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___f_400_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_400_, 0, v_f_399_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_box(0);
v___x_403_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_397_, v_p_396_, v___x_402_, v___f_400_, v___x_401_, v_t_398_, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object* v_m_404_, lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_p_407_, lean_object* v_inst_408_, lean_object* v_t_409_, lean_object* v_f_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___f_411_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_411_, 0, v_f_410_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_box(0);
v___x_414_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_408_, v_p_407_, v___x_413_, v___f_411_, v___x_412_, v_t_409_, v___x_413_);
return v___x_414_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PrefixTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
