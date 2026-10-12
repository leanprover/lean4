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
lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0));
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPrefixTreeNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_6_;
v_res_6_ = l_Lean_instInhabitedPrefixTreeNode___redArg();
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_instInhabitedPrefixTreeNode___redArg();
return v_res_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedPrefixTreeNode___closed__0(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_instInhabitedPrefixTreeNode___redArg();
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_cmp_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_instInhabitedPrefixTreeNode___closed__0, &l_Lean_instInhabitedPrefixTreeNode___closed__0_once, _init_l_Lean_instInhabitedPrefixTreeNode___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode___boxed(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b2_15_, lean_object* v_cmp_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_instInhabitedPrefixTreeNode(v_00_u03b1_14_, v_00_u03b2_15_, v_cmp_16_);
lean_dec_ref(v_cmp_16_);
return v_res_17_;
}
}
lean_object* l_Lean_PrefixTreeNode_empty___redArg(){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = ((lean_object*)(l_Lean_instInhabitedPrefixTreeNode___redArg___closed__0));
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_PrefixTreeNode_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_20_;
v_res_20_ = l_Lean_PrefixTreeNode_empty___redArg();
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_PrefixTreeNode_empty___redArg();
return v_res_22_;
}
}
static lean_object* _init_l_Lean_PrefixTreeNode_empty___closed__0(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_PrefixTreeNode_empty___redArg();
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_cmp_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty___boxed(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_cmp_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_PrefixTreeNode_empty(v_00_u03b1_28_, v_00_u03b2_29_, v_cmp_30_);
lean_dec_ref(v_cmp_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(lean_object* v_cmp_32_, lean_object* v_val_33_, lean_object* v_k_34_){
_start:
{
if (lean_obj_tag(v_k_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v_cmp_32_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_val_33_);
v___x_36_ = lean_box(1);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_head_38_; lean_object* v_tail_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_50_; 
v_head_38_ = lean_ctor_get(v_k_34_, 0);
v_tail_39_ = lean_ctor_get(v_k_34_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_k_34_);
if (v_isSharedCheck_50_ == 0)
{
v___x_41_ = v_k_34_;
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_tail_39_);
lean_inc(v_head_38_);
lean_dec(v_k_34_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_t_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
lean_inc_ref(v_cmp_32_);
v_t_43_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_32_, v_val_33_, v_tail_39_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_box(1);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_32_, v_head_38_, v_t_43_, v___x_45_);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 0);
lean_ctor_set(v___x_41_, 1, v___x_46_);
lean_ctor_set(v___x_41_, 0, v___x_44_);
v___x_48_ = v___x_41_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_cmp_53_, lean_object* v_val_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_53_, v_val_54_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(lean_object* v_cmp_57_, lean_object* v_val_58_, lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
lean_dec_ref(v_cmp_57_);
v_a_61_ = lean_ctor_get(v_x_59_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; 
v_unused_70_ = lean_ctor_get(v_x_59_, 0);
lean_dec(v_unused_70_);
v___x_63_ = v_x_59_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v_x_59_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_val_58_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_a_61_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_88_; 
v_a_71_ = lean_ctor_get(v_x_59_, 0);
v_a_72_ = lean_ctor_get(v_x_59_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_88_ == 0)
{
v___x_74_ = v_x_59_;
v_isShared_75_ = v_isSharedCheck_88_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_inc(v_a_71_);
lean_dec(v_x_59_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_88_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___y_79_; lean_object* v___x_84_; 
v_head_76_ = lean_ctor_get(v_x_60_, 0);
lean_inc_n(v_head_76_, 2);
v_tail_77_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_77_);
lean_dec_ref_known(v_x_60_, 2);
lean_inc(v_a_72_);
lean_inc_ref(v_cmp_57_);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_57_, v_a_72_, v_head_76_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v___x_85_; 
lean_inc_ref(v_cmp_57_);
v___x_85_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_57_, v_val_58_, v_tail_77_);
v___y_79_ = v___x_85_;
goto v___jp_78_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_87_; 
v_val_86_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_84_, 1);
lean_inc_ref(v_cmp_57_);
v___x_87_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_57_, v_val_58_, v_val_86_, v_tail_77_);
v___y_79_ = v___x_87_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_57_, v_head_76_, v___y_79_, v_a_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_80_);
v___x_82_ = v___x_74_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_, lean_object* v_val_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_91_, v_val_92_, v_x_93_, v_x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___redArg(lean_object* v_cmp_96_, lean_object* v_t_97_, lean_object* v_k_98_, lean_object* v_val_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_96_, v_val_99_, v_t_97_, v_k_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_, lean_object* v_t_104_, lean_object* v_k_105_, lean_object* v_val_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_103_, v_val_106_, v_t_104_, v_k_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(lean_object* v_cmp_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v_a_111_; 
lean_dec_ref(v_cmp_108_);
v_a_111_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_a_111_);
lean_dec_ref(v_x_109_);
return v_a_111_;
}
else
{
lean_object* v_a_112_; lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; 
v_a_112_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_a_112_);
lean_dec_ref(v_x_109_);
v_head_113_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_tail_114_);
lean_dec_ref_known(v_x_110_, 2);
lean_inc_ref(v_cmp_108_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_108_, v_a_112_, v_head_113_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_dec(v_tail_114_);
lean_dec_ref(v_cmp_108_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_115_, 1);
v_x_109_ = v_val_117_;
v_x_110_ = v_tail_114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_cmp_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_121_, v_x_122_, v_x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___redArg(lean_object* v_cmp_125_, lean_object* v_t_126_, lean_object* v_k_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_125_, v_t_126_, v_k_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_cmp_131_, lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_cmp_131_, v_t_132_, v_k_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object* v_cmp_135_, lean_object* v_acc_x3f_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_139_; 
lean_dec_ref(v_cmp_135_);
v_a_139_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v_x_137_);
if (lean_obj_tag(v_a_139_) == 0)
{
return v_acc_x3f_136_;
}
else
{
lean_dec(v_acc_x3f_136_);
return v_a_139_;
}
}
else
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v___x_144_; 
v_a_140_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_140_);
v_a_141_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_a_141_);
lean_dec_ref(v_x_137_);
v_head_142_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_head_142_);
v_tail_143_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_tail_143_);
lean_dec_ref_known(v_x_138_, 2);
lean_inc_ref(v_cmp_135_);
v___x_144_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_135_, v_a_141_, v_head_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_dec(v_tail_143_);
lean_dec(v_acc_x3f_136_);
lean_dec_ref(v_cmp_135_);
return v_a_140_;
}
else
{
if (lean_obj_tag(v_a_140_) == 0)
{
lean_object* v_val_145_; 
v_val_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v___x_144_, 1);
v_x_137_ = v_val_145_;
v_x_138_ = v_tail_143_;
goto _start;
}
else
{
lean_object* v_val_147_; 
lean_dec(v_acc_x3f_136_);
v_val_147_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v___x_144_, 1);
v_acc_x3f_136_ = v_a_140_;
v_x_137_ = v_val_147_;
v_x_138_ = v_tail_143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_cmp_151_, lean_object* v_acc_x3f_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_151_, v_acc_x3f_152_, v_x_153_, v_x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(lean_object* v_cmp_156_, lean_object* v_t_157_, lean_object* v_k_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(0);
v___x_160_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_156_, v___x_159_, v_t_157_, v_k_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_cmp_163_, lean_object* v_t_164_, lean_object* v_k_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_cmp_163_, v___x_166_, v_t_164_, v_k_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(lean_object* v_inst_168_, lean_object* v___f_169_, lean_object* v_a_170_, lean_object* v_d_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_168_, v___f_169_, v_d_171_, v_a_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(lean_object* v_inst_173_, lean_object* v_f_174_, lean_object* v_d_175_, lean_object* v_x_176_, lean_object* v_t_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(v_inst_173_, v_f_174_, v_d_175_, v_x_176_, v_t_177_);
lean_dec(v_x_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(lean_object* v_inst_179_, lean_object* v_f_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_toApplicative_183_; lean_object* v_toBind_184_; lean_object* v_toPure_185_; lean_object* v_a_186_; lean_object* v_a_187_; lean_object* v___f_188_; 
v_toApplicative_183_ = lean_ctor_get(v_inst_179_, 0);
v_toBind_184_ = lean_ctor_get(v_inst_179_, 1);
lean_inc(v_toBind_184_);
v_toPure_185_ = lean_ctor_get(v_toApplicative_183_, 1);
v_a_186_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_a_186_);
v_a_187_ = lean_ctor_get(v_a_181_, 1);
lean_inc(v_a_187_);
lean_dec_ref(v_a_181_);
lean_inc(v_f_180_);
lean_inc_ref(v_inst_179_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_188_, 0, v_inst_179_);
lean_closure_set(v___f_188_, 1, v_f_180_);
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc(v_toPure_185_);
lean_dec(v_f_180_);
v___f_189_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_189_, 0, v_inst_179_);
lean_closure_set(v___f_189_, 1, v___f_188_);
lean_closure_set(v___f_189_, 2, v_a_187_);
v___x_190_ = lean_apply_2(v_toPure_185_, lean_box(0), v_a_182_);
v___x_191_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_190_, v___f_189_);
return v___x_191_;
}
else
{
lean_object* v_val_192_; lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_val_192_ = lean_ctor_get(v_a_186_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_a_186_, 1);
v___f_193_ = lean_alloc_closure((void*)(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1), 4, 3);
lean_closure_set(v___f_193_, 0, v_inst_179_);
lean_closure_set(v___f_193_, 1, v___f_188_);
lean_closure_set(v___f_193_, 2, v_a_187_);
v___x_194_ = lean_apply_2(v_f_180_, v_val_192_, v_a_182_);
v___x_195_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_194_, v___f_193_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(lean_object* v_inst_196_, lean_object* v_f_197_, lean_object* v_d_198_, lean_object* v_x_199_, lean_object* v_t_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_196_, v_f_197_, v_t_200_, v_d_198_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(lean_object* v_m_202_, lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_00_u03c3_205_, lean_object* v_inst_206_, lean_object* v_cmp_207_, lean_object* v_f_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_206_, v_f_208_, v_a_209_, v_a_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___boxed(lean_object* v_m_212_, lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_00_u03c3_215_, lean_object* v_inst_216_, lean_object* v_cmp_217_, lean_object* v_f_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(v_m_212_, v_00_u03b1_213_, v_00_u03b2_214_, v_00_u03c3_215_, v_inst_216_, v_cmp_217_, v_f_218_, v_a_219_, v_a_220_);
lean_dec_ref(v_cmp_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(lean_object* v_inst_222_, lean_object* v_cmp_223_, lean_object* v_init_224_, lean_object* v_f_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
if (lean_obj_tag(v_a_226_) == 0)
{
lean_object* v___x_229_; 
lean_dec(v_init_224_);
lean_dec_ref(v_cmp_223_);
v___x_229_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_222_, v_f_225_, v_a_227_, v_a_228_);
return v___x_229_;
}
else
{
lean_object* v_toApplicative_230_; lean_object* v_toPure_231_; lean_object* v_head_232_; lean_object* v_tail_233_; lean_object* v_a_234_; lean_object* v___x_235_; 
v_toApplicative_230_ = lean_ctor_get(v_inst_222_, 0);
v_toPure_231_ = lean_ctor_get(v_toApplicative_230_, 1);
v_head_232_ = lean_ctor_get(v_a_226_, 0);
lean_inc(v_head_232_);
v_tail_233_ = lean_ctor_get(v_a_226_, 1);
lean_inc(v_tail_233_);
lean_dec_ref_known(v_a_226_, 2);
v_a_234_ = lean_ctor_get(v_a_227_, 1);
lean_inc(v_a_234_);
lean_dec_ref(v_a_227_);
lean_inc_ref(v_cmp_223_);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_223_, v_a_234_, v_head_232_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
lean_inc(v_toPure_231_);
lean_dec(v_tail_233_);
lean_dec(v_a_228_);
lean_dec(v_f_225_);
lean_dec_ref(v_cmp_223_);
lean_dec_ref(v_inst_222_);
v___x_236_ = lean_apply_2(v_toPure_231_, lean_box(0), v_init_224_);
return v___x_236_;
}
else
{
lean_object* v_val_237_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_235_, 1);
v_a_226_ = v_tail_233_;
v_a_227_ = v_val_237_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_object* v_m_239_, lean_object* v_00_u03b1_240_, lean_object* v_00_u03b2_241_, lean_object* v_00_u03c3_242_, lean_object* v_inst_243_, lean_object* v_cmp_244_, lean_object* v_init_245_, lean_object* v_f_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_243_, v_cmp_244_, v_init_245_, v_f_246_, v_a_247_, v_a_248_, v_a_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___redArg(lean_object* v_inst_251_, lean_object* v_cmp_252_, lean_object* v_t_253_, lean_object* v_k_254_, lean_object* v_init_255_, lean_object* v_f_256_){
_start:
{
lean_object* v___x_257_; 
lean_inc(v_init_255_);
v___x_257_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_251_, v_cmp_252_, v_init_255_, v_f_256_, v_k_254_, v_t_253_, v_init_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object* v_m_258_, lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_00_u03c3_261_, lean_object* v_inst_262_, lean_object* v_cmp_263_, lean_object* v_t_264_, lean_object* v_k_265_, lean_object* v_init_266_, lean_object* v_f_267_){
_start:
{
lean_object* v___x_268_; 
lean_inc(v_init_266_);
v___x_268_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_262_, v_cmp_263_, v_init_266_, v_f_267_, v_k_265_, v_t_264_, v_init_266_);
return v___x_268_;
}
}
lean_object* l_Lean_PrefixTree_empty___redArg(){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_PrefixTree_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_271_;
v_res_271_ = l_Lean_PrefixTree_empty___redArg();
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___redArg___boxed(lean_object* v___dummy_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_PrefixTree_empty___redArg();
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_p_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_p_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_PrefixTree_empty(v_00_u03b1_278_, v_00_u03b2_279_, v_p_280_);
lean_dec_ref(v_p_280_);
return v_res_281_;
}
}
lean_object* l_Lean_instInhabitedPrefixTree___redArg(){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_283_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPrefixTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_284_;
v_res_284_ = l_Lean_instInhabitedPrefixTree___redArg();
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___redArg___boxed(lean_object* v___dummy_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_instInhabitedPrefixTree___redArg();
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_p_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_p_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_instInhabitedPrefixTree(v_00_u03b1_291_, v_00_u03b2_292_, v_p_293_);
lean_dec_ref(v_p_293_);
return v_res_294_;
}
}
lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg(){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionPrefixTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_297_;
v_res_297_ = l_Lean_instEmptyCollectionPrefixTree___redArg();
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(lean_object* v___dummy_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_instEmptyCollectionPrefixTree___redArg();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_p_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_PrefixTreeNode_empty___closed__0, &l_Lean_PrefixTreeNode_empty___closed__0_once, _init_l_Lean_PrefixTreeNode_empty___closed__0);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_p_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_instEmptyCollectionPrefixTree(v_00_u03b1_304_, v_00_u03b2_305_, v_p_306_);
lean_dec_ref(v_p_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___redArg(lean_object* v_p_308_, lean_object* v_t_309_, lean_object* v_k_310_, lean_object* v_v_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_308_, v_v_311_, v_t_309_, v_k_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_p_315_, lean_object* v_t_316_, lean_object* v_k_317_, lean_object* v_v_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_p_315_, v_v_318_, v_t_316_, v_k_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___redArg(lean_object* v_p_320_, lean_object* v_t_321_, lean_object* v_k_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_320_, v_t_321_, v_k_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_p_326_, lean_object* v_t_327_, lean_object* v_k_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(v_p_326_, v_t_327_, v_k_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(lean_object* v_p_330_, lean_object* v_t_331_, lean_object* v_k_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(0);
v___x_334_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_330_, v___x_333_, v_t_331_, v_k_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_findLongestPrefix_x3f(lean_object* v_00_u03b1_335_, lean_object* v_00_u03b2_336_, lean_object* v_p_337_, lean_object* v_t_338_, lean_object* v_k_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(v_p_337_, v___x_340_, v_t_338_, v_k_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___redArg(lean_object* v_p_342_, lean_object* v_inst_343_, lean_object* v_t_344_, lean_object* v_k_345_, lean_object* v_init_346_, lean_object* v_f_347_){
_start:
{
lean_object* v___x_348_; 
lean_inc(v_init_346_);
v___x_348_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_343_, v_p_342_, v_init_346_, v_f_347_, v_k_345_, v_t_344_, v_init_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object* v_m_349_, lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_p_352_, lean_object* v_00_u03c3_353_, lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_k_356_, lean_object* v_init_357_, lean_object* v_f_358_){
_start:
{
lean_object* v___x_359_; 
lean_inc(v_init_357_);
v___x_359_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_354_, v_p_352_, v_init_357_, v_f_358_, v_k_356_, v_t_355_, v_init_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___redArg(lean_object* v_p_360_, lean_object* v_inst_361_, lean_object* v_t_362_, lean_object* v_init_363_, lean_object* v_f_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
lean_inc(v_init_363_);
v___x_366_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_361_, v_p_360_, v_init_363_, v_f_364_, v___x_365_, v_t_362_, v_init_363_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object* v_m_367_, lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_p_370_, lean_object* v_00_u03c3_371_, lean_object* v_inst_372_, lean_object* v_t_373_, lean_object* v_init_374_, lean_object* v_f_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_box(0);
lean_inc(v_init_374_);
v___x_377_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_372_, v_p_370_, v_init_374_, v_f_375_, v___x_376_, v_t_373_, v_init_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg___lam__0(lean_object* v_f_378_, lean_object* v_b_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_apply_1(v_f_378_, v_b_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___redArg(lean_object* v_p_382_, lean_object* v_inst_383_, lean_object* v_t_384_, lean_object* v_k_385_, lean_object* v_f_386_){
_start:
{
lean_object* v___f_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___f_387_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_387_, 0, v_f_386_);
v___x_388_ = lean_box(0);
v___x_389_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_383_, v_p_382_, v___x_388_, v___f_387_, v_k_385_, v_t_384_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object* v_m_390_, lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_p_393_, lean_object* v_inst_394_, lean_object* v_t_395_, lean_object* v_k_396_, lean_object* v_f_397_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___f_398_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_398_, 0, v_f_397_);
v___x_399_ = lean_box(0);
v___x_400_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_394_, v_p_393_, v___x_399_, v___f_398_, v_k_396_, v_t_395_, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___redArg(lean_object* v_p_401_, lean_object* v_inst_402_, lean_object* v_t_403_, lean_object* v_f_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___f_405_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_405_, 0, v_f_404_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_box(0);
v___x_408_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_402_, v_p_401_, v___x_407_, v___f_405_, v___x_406_, v_t_403_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object* v_m_409_, lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_p_412_, lean_object* v_inst_413_, lean_object* v_t_414_, lean_object* v_f_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___f_416_ = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_416_, 0, v_f_415_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_box(0);
v___x_419_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(v_inst_413_, v_p_412_, v___x_418_, v___f_416_, v___x_417_, v_t_414_, v___x_418_);
return v___x_419_;
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
