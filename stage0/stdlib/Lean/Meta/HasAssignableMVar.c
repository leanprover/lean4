// Lean compiler output
// Module: Lean.Meta.HasAssignableMVar
// Imports: public import Lean.Meta.Basic
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDecl(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "hasAssignableMVar"};
static const lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_hasAssignableMVar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_hasAssignableMVar___closed__0;
static lean_once_cell_t l_Lean_Meta_hasAssignableMVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_hasAssignableMVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_mctx_5_; lean_object* v_levelAssignDepth_6_; lean_object* v_decl_7_; lean_object* v_depth_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_mctx_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_mctx_5_);
lean_dec(v___x_4_);
v_levelAssignDepth_6_ = lean_ctor_get(v_mctx_5_, 1);
lean_inc(v_levelAssignDepth_6_);
v_decl_7_ = l_Lean_MetavarContext_getLevelDecl(v_mctx_5_, v_mvarId_1_);
lean_dec_ref(v_mctx_5_);
v_depth_8_ = lean_ctor_get(v_decl_7_, 0);
lean_inc(v_depth_8_);
lean_dec_ref(v_decl_7_);
v___x_9_ = lean_nat_dec_le(v_levelAssignDepth_6_, v_depth_8_);
lean_dec(v_depth_8_);
lean_dec(v_levelAssignDepth_6_);
v___x_10_ = lean_box(v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg___boxed(lean_object* v_mvarId_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_mvarId_12_, v___y_13_);
lean_dec(v___y_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(lean_object* v_mvarId_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_mvarId_16_, v___y_18_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___boxed(lean_object* v_mvarId_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(v_mvarId_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object* v_x_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v_lvl_u2081_47_; lean_object* v_lvl_u2082_48_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v___y_52_; 
switch(lean_obj_tag(v_x_30_))
{
case 1:
{
lean_object* v_a_57_; uint8_t v___x_58_; 
v_a_57_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_57_);
lean_dec_ref_known(v_x_30_, 1);
v___x_58_ = l_Lean_Level_hasMVar(v_a_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_a_57_);
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
else
{
v_x_30_ = v_a_57_;
goto _start;
}
}
case 2:
{
lean_object* v_a_62_; lean_object* v_a_63_; 
v_a_62_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_a_63_);
lean_dec_ref_known(v_x_30_, 2);
v_lvl_u2081_47_ = v_a_62_;
v_lvl_u2082_48_ = v_a_63_;
v___y_49_ = v_a_31_;
v___y_50_ = v_a_32_;
v___y_51_ = v_a_33_;
v___y_52_ = v_a_34_;
goto v___jp_46_;
}
case 3:
{
lean_object* v_a_64_; lean_object* v_a_65_; 
v_a_64_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_64_);
v_a_65_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_a_65_);
lean_dec_ref_known(v_x_30_, 2);
v_lvl_u2081_47_ = v_a_64_;
v_lvl_u2082_48_ = v_a_65_;
v___y_49_ = v_a_31_;
v___y_50_ = v_a_32_;
v___y_51_ = v_a_33_;
v___y_52_ = v_a_34_;
goto v___jp_46_;
}
case 5:
{
lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_66_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v_x_30_, 1);
v___x_67_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_a_66_, v_a_32_);
return v___x_67_;
}
default: 
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_x_30_);
v___x_68_ = 0;
v___x_69_ = lean_box(v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
v___jp_36_:
{
uint8_t v___x_42_; 
v___x_42_ = l_Lean_Level_hasMVar(v___y_37_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v___y_37_);
v___x_43_ = lean_box(v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
else
{
v_x_30_ = v___y_37_;
v_a_31_ = v___y_40_;
v_a_32_ = v___y_41_;
v_a_33_ = v___y_39_;
v_a_34_ = v___y_38_;
goto _start;
}
}
v___jp_46_:
{
uint8_t v___x_53_; 
v___x_53_ = l_Lean_Level_hasMVar(v_lvl_u2081_47_);
if (v___x_53_ == 0)
{
lean_dec(v_lvl_u2081_47_);
v___y_37_ = v_lvl_u2082_48_;
v___y_38_ = v___y_52_;
v___y_39_ = v___y_51_;
v___y_40_ = v___y_49_;
v___y_41_ = v___y_50_;
goto v___jp_36_;
}
else
{
lean_object* v___x_54_; lean_object* v_a_55_; uint8_t v___x_56_; 
v___x_54_ = l_Lean_Meta_hasAssignableLevelMVar(v_lvl_u2081_47_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v___x_56_ = lean_unbox(v_a_55_);
if (v___x_56_ == 0)
{
lean_dec_ref(v___x_54_);
v___y_37_ = v_lvl_u2082_48_;
v___y_38_ = v___y_52_;
v___y_39_ = v___y_51_;
v___y_40_ = v___y_49_;
v___y_41_ = v___y_50_;
goto v___jp_36_;
}
else
{
lean_dec(v_lvl_u2082_48_);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar___boxed(lean_object* v_x_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_hasAssignableLevelMVar(v_x_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(lean_object* v_mvarId_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; lean_object* v_mctx_82_; lean_object* v_decl_83_; lean_object* v_depth_84_; lean_object* v_depth_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_mctx_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_mctx_82_);
lean_dec(v___x_81_);
v_decl_83_ = l_Lean_MetavarContext_getDecl(v_mctx_82_, v_mvarId_78_);
v_depth_84_ = lean_ctor_get(v_decl_83_, 3);
lean_inc(v_depth_84_);
lean_dec_ref(v_decl_83_);
v_depth_85_ = lean_ctor_get(v_mctx_82_, 0);
lean_inc(v_depth_85_);
lean_dec_ref(v_mctx_82_);
v___x_86_ = lean_nat_dec_eq(v_depth_84_, v_depth_85_);
lean_dec(v_depth_85_);
lean_dec(v_depth_84_);
v___x_87_ = lean_box(v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg___boxed(lean_object* v_mvarId_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_89_, v___y_90_);
lean_dec(v___y_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(lean_object* v_mvarId_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_93_, v___y_96_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___boxed(lean_object* v_mvarId_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(v_mvarId_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = 0;
v___x_116_ = lean_box(v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_120_; lean_object* v_a_121_; uint8_t v___x_122_; 
v_head_118_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_head_118_);
v_tail_119_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_tail_119_);
lean_dec_ref_known(v_x_109_, 2);
v___x_120_ = l_Lean_Meta_hasAssignableLevelMVar(v_head_118_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v___x_122_ = lean_unbox(v_a_121_);
if (v___x_122_ == 0)
{
lean_dec_ref(v___x_120_);
v_x_109_ = v_tail_119_;
goto _start;
}
else
{
lean_dec(v_tail_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg___boxed(lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object* v_a_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
else
{
lean_object* v_key_134_; lean_object* v_tail_135_; uint8_t v___x_136_; 
v_key_134_ = lean_ctor_get(v_x_132_, 0);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v___x_136_ = lean_expr_eqv(v_key_134_, v_a_131_);
if (v___x_136_ == 0)
{
v_x_132_ = v_tail_135_;
goto _start;
}
else
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec_ref(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object* v_m_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_buckets_144_; lean_object* v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v_fold_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_buckets_144_ = lean_ctor_get(v_m_142_, 1);
v___x_145_ = lean_array_get_size(v_buckets_144_);
v___x_146_ = l_Lean_Expr_hash(v_a_143_);
v___x_147_ = 32ULL;
v___x_148_ = lean_uint64_shift_right(v___x_146_, v___x_147_);
v_fold_149_ = lean_uint64_xor(v___x_146_, v___x_148_);
v___x_150_ = 16ULL;
v___x_151_ = lean_uint64_shift_right(v_fold_149_, v___x_150_);
v___x_152_ = lean_uint64_xor(v_fold_149_, v___x_151_);
v___x_153_ = lean_uint64_to_usize(v___x_152_);
v___x_154_ = lean_usize_of_nat(v___x_145_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_usize_land(v___x_153_, v___x_156_);
v___x_158_ = lean_array_uget_borrowed(v_buckets_144_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_143_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object* v_m_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_160_, v_a_161_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_m_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
return v_x_164_;
}
else
{
lean_object* v_key_166_; lean_object* v_value_167_; lean_object* v_tail_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_191_; 
v_key_166_ = lean_ctor_get(v_x_165_, 0);
v_value_167_ = lean_ctor_get(v_x_165_, 1);
v_tail_168_ = lean_ctor_get(v_x_165_, 2);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_191_ == 0)
{
v___x_170_ = v_x_165_;
v_isShared_171_ = v_isSharedCheck_191_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_tail_168_);
lean_inc(v_value_167_);
lean_inc(v_key_166_);
lean_dec(v_x_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_191_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v_fold_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_172_ = lean_array_get_size(v_x_164_);
v___x_173_ = l_Lean_Expr_hash(v_key_166_);
v___x_174_ = 32ULL;
v___x_175_ = lean_uint64_shift_right(v___x_173_, v___x_174_);
v_fold_176_ = lean_uint64_xor(v___x_173_, v___x_175_);
v___x_177_ = 16ULL;
v___x_178_ = lean_uint64_shift_right(v_fold_176_, v___x_177_);
v___x_179_ = lean_uint64_xor(v_fold_176_, v___x_178_);
v___x_180_ = lean_uint64_to_usize(v___x_179_);
v___x_181_ = lean_usize_of_nat(v___x_172_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_sub(v___x_181_, v___x_182_);
v___x_184_ = lean_usize_land(v___x_180_, v___x_183_);
v___x_185_ = lean_array_uget_borrowed(v_x_164_, v___x_184_);
lean_inc(v___x_185_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 2, v___x_185_);
v___x_187_ = v___x_170_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_key_166_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_value_167_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v___x_185_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_array_uset(v_x_164_, v___x_184_, v___x_187_);
v_x_164_ = v___x_188_;
v_x_165_ = v_tail_168_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_192_, lean_object* v_source_193_, lean_object* v_target_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_get_size(v_source_193_);
v___x_196_ = lean_nat_dec_lt(v_i_192_, v___x_195_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_source_193_);
lean_dec(v_i_192_);
return v_target_194_;
}
else
{
lean_object* v_es_197_; lean_object* v___x_198_; lean_object* v_source_199_; lean_object* v_target_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_es_197_ = lean_array_fget(v_source_193_, v_i_192_);
v___x_198_ = lean_box(0);
v_source_199_ = lean_array_fset(v_source_193_, v_i_192_, v___x_198_);
v_target_200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_194_, v_es_197_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_i_192_, v___x_201_);
lean_dec(v_i_192_);
v_i_192_ = v___x_202_;
v_source_193_ = v_source_199_;
v_target_194_ = v_target_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object* v_data_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_nbuckets_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_205_ = lean_array_get_size(v_data_204_);
v___x_206_ = lean_unsigned_to_nat(2u);
v_nbuckets_207_ = lean_nat_mul(v___x_205_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_box(0);
v___x_210_ = lean_mk_array(v_nbuckets_207_, v___x_209_);
v___x_211_ = lean_array_propagate_mark(v_data_204_, v___x_210_);
v___x_212_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v___x_208_, v_data_204_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object* v_m_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v_size_216_; lean_object* v_buckets_217_; lean_object* v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v_fold_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v_bkt_231_; uint8_t v___x_232_; 
v_size_216_ = lean_ctor_get(v_m_213_, 0);
v_buckets_217_ = lean_ctor_get(v_m_213_, 1);
v___x_218_ = lean_array_get_size(v_buckets_217_);
v___x_219_ = l_Lean_Expr_hash(v_a_214_);
v___x_220_ = 32ULL;
v___x_221_ = lean_uint64_shift_right(v___x_219_, v___x_220_);
v_fold_222_ = lean_uint64_xor(v___x_219_, v___x_221_);
v___x_223_ = 16ULL;
v___x_224_ = lean_uint64_shift_right(v_fold_222_, v___x_223_);
v___x_225_ = lean_uint64_xor(v_fold_222_, v___x_224_);
v___x_226_ = lean_uint64_to_usize(v___x_225_);
v___x_227_ = lean_usize_of_nat(v___x_218_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_sub(v___x_227_, v___x_228_);
v___x_230_ = lean_usize_land(v___x_226_, v___x_229_);
v_bkt_231_ = lean_array_uget_borrowed(v_buckets_217_, v___x_230_);
v___x_232_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_214_, v_bkt_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_253_; 
lean_inc_ref(v_buckets_217_);
lean_inc(v_size_216_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_m_213_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; 
v_unused_254_ = lean_ctor_get(v_m_213_, 1);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_m_213_, 0);
lean_dec(v_unused_255_);
v___x_234_ = v_m_213_;
v_isShared_235_ = v_isSharedCheck_253_;
goto v_resetjp_233_;
}
else
{
lean_dec(v_m_213_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_253_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v_size_x27_237_; lean_object* v___x_238_; lean_object* v_buckets_x27_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v_size_x27_237_ = lean_nat_add(v_size_216_, v___x_236_);
lean_dec(v_size_216_);
lean_inc(v_bkt_231_);
v___x_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_238_, 0, v_a_214_);
lean_ctor_set(v___x_238_, 1, v_b_215_);
lean_ctor_set(v___x_238_, 2, v_bkt_231_);
v_buckets_x27_239_ = lean_array_uset(v_buckets_217_, v___x_230_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(4u);
v___x_241_ = lean_nat_mul(v_size_x27_237_, v___x_240_);
v___x_242_ = lean_unsigned_to_nat(3u);
v___x_243_ = lean_nat_div(v___x_241_, v___x_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_array_get_size(v_buckets_x27_239_);
v___x_245_ = lean_nat_dec_le(v___x_243_, v___x_244_);
lean_dec(v___x_243_);
if (v___x_245_ == 0)
{
lean_object* v_val_246_; lean_object* v___x_248_; 
v_val_246_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_buckets_x27_239_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v_val_246_);
lean_ctor_set(v___x_234_, 0, v_size_x27_237_);
v___x_248_ = v___x_234_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_size_x27_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_val_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v___x_251_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v_buckets_x27_239_);
lean_ctor_set(v___x_234_, 0, v_size_x27_237_);
v___x_251_ = v___x_234_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_size_x27_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_buckets_x27_239_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_dec(v_b_215_);
lean_dec_ref(v_a_214_);
return v_m_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_d_265_; lean_object* v_b_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; 
switch(lean_obj_tag(v_e_257_))
{
case 2:
{
lean_object* v_mvarId_286_; lean_object* v___x_287_; 
v_mvarId_286_ = lean_ctor_get(v_e_257_, 0);
lean_inc(v_mvarId_286_);
lean_dec_ref_known(v_e_257_, 1);
v___x_287_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_286_, v_a_260_);
return v___x_287_;
}
case 3:
{
lean_object* v_u_288_; lean_object* v___x_289_; 
v_u_288_ = lean_ctor_get(v_e_257_, 0);
lean_inc(v_u_288_);
lean_dec_ref_known(v_e_257_, 1);
v___x_289_ = l_Lean_Meta_hasAssignableLevelMVar(v_u_288_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_289_;
}
case 4:
{
lean_object* v_us_290_; lean_object* v___x_291_; 
v_us_290_ = lean_ctor_get(v_e_257_, 1);
lean_inc(v_us_290_);
lean_dec_ref_known(v_e_257_, 2);
v___x_291_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_us_290_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_291_;
}
case 5:
{
lean_object* v_fn_292_; lean_object* v_arg_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_fn_292_ = lean_ctor_get(v_e_257_, 0);
lean_inc_ref(v_fn_292_);
v_arg_293_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_arg_293_);
lean_dec_ref_known(v_e_257_, 2);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_295_ = l_Lean_Core_checkSystem(v___x_294_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
lean_dec_ref_known(v___x_295_, 1);
v___x_296_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_fn_292_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = lean_unbox(v_a_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_296_, 1);
v___x_299_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_arg_293_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_299_;
}
else
{
lean_dec_ref(v_arg_293_);
return v___x_296_;
}
}
else
{
lean_dec_ref(v_arg_293_);
return v___x_296_;
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_fn_292_);
v_a_300_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_295_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
case 6:
{
lean_object* v_binderType_308_; lean_object* v_body_309_; 
v_binderType_308_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_binderType_308_);
v_body_309_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_body_309_);
lean_dec_ref_known(v_e_257_, 3);
v_d_265_ = v_binderType_308_;
v_b_266_ = v_body_309_;
v___y_267_ = v_a_258_;
v___y_268_ = v_a_259_;
v___y_269_ = v_a_260_;
v___y_270_ = v_a_261_;
v___y_271_ = v_a_262_;
goto v___jp_264_;
}
case 7:
{
lean_object* v_binderType_310_; lean_object* v_body_311_; 
v_binderType_310_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_binderType_310_);
v_body_311_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_body_311_);
lean_dec_ref_known(v_e_257_, 3);
v_d_265_ = v_binderType_310_;
v_b_266_ = v_body_311_;
v___y_267_ = v_a_258_;
v___y_268_ = v_a_259_;
v___y_269_ = v_a_260_;
v___y_270_ = v_a_261_;
v___y_271_ = v_a_262_;
goto v___jp_264_;
}
case 8:
{
lean_object* v_type_312_; lean_object* v_value_313_; lean_object* v_body_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_type_312_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_type_312_);
v_value_313_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_value_313_);
v_body_314_ = lean_ctor_get(v_e_257_, 3);
lean_inc_ref(v_body_314_);
lean_dec_ref_known(v_e_257_, 4);
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_316_ = l_Lean_Core_checkSystem(v___x_315_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; 
lean_dec_ref_known(v___x_316_, 1);
v___x_317_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_type_312_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; uint8_t v___x_319_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v___x_319_ = lean_unbox(v_a_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref_known(v___x_317_, 1);
v___x_320_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_value_313_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; uint8_t v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v___x_322_ = lean_unbox(v_a_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref_known(v___x_320_, 1);
v___x_323_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_body_314_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_323_;
}
else
{
lean_dec_ref(v_body_314_);
return v___x_320_;
}
}
else
{
lean_dec_ref(v_body_314_);
return v___x_320_;
}
}
else
{
lean_dec_ref(v_body_314_);
lean_dec_ref(v_value_313_);
return v___x_317_;
}
}
else
{
lean_dec_ref(v_body_314_);
lean_dec_ref(v_value_313_);
return v___x_317_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_body_314_);
lean_dec_ref(v_value_313_);
lean_dec_ref(v_type_312_);
v_a_324_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_316_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_316_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
case 10:
{
lean_object* v_expr_332_; lean_object* v___x_333_; 
v_expr_332_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_expr_332_);
lean_dec_ref_known(v_e_257_, 2);
v___x_333_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_expr_332_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_333_;
}
case 11:
{
lean_object* v_struct_334_; lean_object* v___x_335_; 
v_struct_334_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_struct_334_);
lean_dec_ref_known(v_e_257_, 3);
v___x_335_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_struct_334_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_335_;
}
default: 
{
uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_e_257_);
v___x_336_ = 0;
v___x_337_ = lean_box(v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
v___jp_264_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_273_ = l_Lean_Core_checkSystem(v___x_272_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; 
lean_dec_ref_known(v___x_273_, 1);
v___x_274_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_d_265_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; uint8_t v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v___x_276_ = lean_unbox(v_a_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref_known(v___x_274_, 1);
v___x_277_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_b_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_277_;
}
else
{
lean_dec_ref(v_b_266_);
return v___x_274_;
}
}
else
{
lean_dec_ref(v_b_266_);
return v___x_274_;
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_b_266_);
lean_dec_ref(v_d_265_);
v_a_278_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_273_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_273_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object* v_e_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_Lean_Expr_hasMVar(v_e_339_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref(v_e_339_);
v___x_347_ = lean_box(v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
else
{
uint8_t v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = 0;
v___x_350_ = lean_st_ref_get(v_a_340_);
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v___x_350_, v_e_339_);
lean_dec(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_352_ = lean_st_ref_take(v_a_340_);
v___x_353_ = lean_box(0);
lean_inc_ref(v_e_339_);
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_352_, v_e_339_, v___x_353_);
v___x_355_ = lean_st_ref_put(v_a_340_, v___x_354_);
v___x_356_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v_e_339_);
v___x_357_ = lean_box(v___x_349_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_e_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object* v_e_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object* v_00_u03b2_391_, lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_392_, v_a_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object* v_00_u03b2_395_, lean_object* v_m_396_, lean_object* v_a_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(v_00_u03b2_395_, v_m_396_, v_a_397_);
lean_dec_ref(v_a_397_);
lean_dec_ref(v_m_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_a_402_, lean_object* v_b_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_401_, v_a_402_, v_b_403_);
return v___x_404_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object* v_00_u03b2_405_, lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_409_, lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(v_00_u03b2_409_, v_a_410_, v_x_411_);
lean_dec(v_x_411_);
lean_dec_ref(v_a_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object* v_00_u03b2_414_, lean_object* v_data_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_data_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_417_, lean_object* v_i_418_, lean_object* v_source_419_, lean_object* v_target_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v_i_418_, v_source_419_, v_target_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_423_, v_x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = lean_unsigned_to_nat(16u);
v___x_428_ = lean_mk_array(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__0, &l_Lean_Meta_hasAssignableMVar___closed__0_once, _init_l_Lean_Meta_hasAssignableMVar___closed__0);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_Lean_Expr_hasMVar(v_e_432_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_e_432_);
v___x_439_ = lean_box(v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__1, &l_Lean_Meta_hasAssignableMVar___closed__1_once, _init_l_Lean_Meta_hasAssignableMVar___closed__1);
v___x_442_ = lean_st_mk_ref(v___x_441_);
v___x_443_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_432_, v___x_442_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_st_ref_get(v___x_442_);
lean_dec(v___x_442_);
lean_dec(v___x_448_);
if (v_isShared_447_ == 0)
{
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_444_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_dec(v___x_442_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* v_e_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_hasAssignableMVar(v_e_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_459_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_HasAssignableMVar(builtin);
}
#ifdef __cplusplus
}
#endif
