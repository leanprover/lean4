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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; uint8_t v_a_43_; lean_object* v_lvl_u2081_49_; lean_object* v_lvl_u2082_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; 
switch(lean_obj_tag(v_x_30_))
{
case 1:
{
lean_object* v_a_61_; uint8_t v___x_62_; 
v_a_61_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v_x_30_);
v___x_62_ = l_Lean_Level_hasMVar(v_a_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_a_61_);
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
else
{
v_x_30_ = v_a_61_;
goto _start;
}
}
case 2:
{
lean_object* v_a_66_; lean_object* v_a_67_; 
v_a_66_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_66_);
v_a_67_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_a_67_);
lean_dec_ref(v_x_30_);
v_lvl_u2081_49_ = v_a_66_;
v_lvl_u2082_50_ = v_a_67_;
v___y_51_ = v_a_31_;
v___y_52_ = v_a_32_;
v___y_53_ = v_a_33_;
v___y_54_ = v_a_34_;
goto v___jp_48_;
}
case 3:
{
lean_object* v_a_68_; lean_object* v_a_69_; 
v_a_68_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_a_69_);
lean_dec_ref(v_x_30_);
v_lvl_u2081_49_ = v_a_68_;
v_lvl_u2082_50_ = v_a_69_;
v___y_51_ = v_a_31_;
v___y_52_ = v_a_32_;
v___y_53_ = v_a_33_;
v___y_54_ = v_a_34_;
goto v___jp_48_;
}
case 5:
{
lean_object* v_a_70_; lean_object* v___x_71_; 
v_a_70_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v_x_30_);
v___x_71_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_a_70_, v_a_32_);
return v___x_71_;
}
default: 
{
uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_x_30_);
v___x_72_ = 0;
v___x_73_ = lean_box(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
v___jp_36_:
{
if (v_a_43_ == 0)
{
uint8_t v___x_44_; 
lean_dec_ref(v___y_42_);
v___x_44_ = l_Lean_Level_hasMVar(v___y_39_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v___y_39_);
v___x_45_ = lean_box(v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
else
{
v_x_30_ = v___y_39_;
v_a_31_ = v___y_38_;
v_a_32_ = v___y_37_;
v_a_33_ = v___y_41_;
v_a_34_ = v___y_40_;
goto _start;
}
}
else
{
lean_dec(v___y_39_);
return v___y_42_;
}
}
v___jp_48_:
{
uint8_t v___x_55_; 
v___x_55_ = l_Lean_Level_hasMVar(v_lvl_u2081_49_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_lvl_u2081_49_);
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
v___y_37_ = v___y_52_;
v___y_38_ = v___y_51_;
v___y_39_ = v_lvl_u2082_50_;
v___y_40_ = v___y_54_;
v___y_41_ = v___y_53_;
v___y_42_ = v___x_57_;
v_a_43_ = v___x_55_;
goto v___jp_36_;
}
else
{
lean_object* v___x_58_; lean_object* v_a_59_; uint8_t v___x_60_; 
v___x_58_ = l_Lean_Meta_hasAssignableLevelMVar(v_lvl_u2081_49_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
v___x_60_ = lean_unbox(v_a_59_);
lean_dec(v_a_59_);
v___y_37_ = v___y_52_;
v___y_38_ = v___y_51_;
v___y_39_ = v_lvl_u2082_50_;
v___y_40_ = v___y_54_;
v___y_41_ = v___y_53_;
v___y_42_ = v___x_58_;
v_a_43_ = v___x_60_;
goto v___jp_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar___boxed(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_hasAssignableLevelMVar(v_x_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(lean_object* v_mvarId_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v_mctx_86_; lean_object* v_decl_87_; lean_object* v_depth_88_; lean_object* v_depth_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_85_ = lean_st_ref_get(v___y_83_);
v_mctx_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref_n(v_mctx_86_, 2);
lean_dec(v___x_85_);
v_decl_87_ = l_Lean_MetavarContext_getDecl(v_mctx_86_, v_mvarId_82_);
v_depth_88_ = lean_ctor_get(v_decl_87_, 3);
lean_inc(v_depth_88_);
lean_dec_ref(v_decl_87_);
v_depth_89_ = lean_ctor_get(v_mctx_86_, 0);
lean_inc(v_depth_89_);
lean_dec_ref(v_mctx_86_);
v___x_90_ = lean_nat_dec_eq(v_depth_88_, v_depth_89_);
lean_dec(v_depth_89_);
lean_dec(v_depth_88_);
v___x_91_ = lean_box(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg___boxed(lean_object* v_mvarId_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_93_, v___y_94_);
lean_dec(v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(lean_object* v_mvarId_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_97_, v___y_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___boxed(lean_object* v_mvarId_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(v_mvarId_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = 0;
v___x_120_ = lean_box(v___x_119_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_124_; lean_object* v_a_125_; uint8_t v___x_126_; 
v_head_122_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_tail_123_);
lean_dec_ref(v_x_113_);
v___x_124_ = l_Lean_Meta_hasAssignableLevelMVar(v_head_122_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
v___x_126_ = lean_unbox(v_a_125_);
lean_dec(v_a_125_);
if (v___x_126_ == 0)
{
lean_dec_ref(v___x_124_);
v_x_113_ = v_tail_123_;
goto _start;
}
else
{
lean_dec(v_tail_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg___boxed(lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_134_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object* v_a_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
else
{
lean_object* v_key_138_; lean_object* v_tail_139_; uint8_t v___x_140_; 
v_key_138_ = lean_ctor_get(v_x_136_, 0);
v_tail_139_ = lean_ctor_get(v_x_136_, 2);
v___x_140_ = lean_expr_eqv(v_key_138_, v_a_135_);
if (v___x_140_ == 0)
{
v_x_136_ = v_tail_139_;
goto _start;
}
else
{
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_142_, v_x_143_);
lean_dec(v_x_143_);
lean_dec_ref(v_a_142_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object* v_m_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_buckets_148_; lean_object* v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v_fold_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_buckets_148_ = lean_ctor_get(v_m_146_, 1);
v___x_149_ = lean_array_get_size(v_buckets_148_);
v___x_150_ = l_Lean_Expr_hash(v_a_147_);
v___x_151_ = 32ULL;
v___x_152_ = lean_uint64_shift_right(v___x_150_, v___x_151_);
v_fold_153_ = lean_uint64_xor(v___x_150_, v___x_152_);
v___x_154_ = 16ULL;
v___x_155_ = lean_uint64_shift_right(v_fold_153_, v___x_154_);
v___x_156_ = lean_uint64_xor(v_fold_153_, v___x_155_);
v___x_157_ = lean_uint64_to_usize(v___x_156_);
v___x_158_ = lean_usize_of_nat(v___x_149_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_sub(v___x_158_, v___x_159_);
v___x_161_ = lean_usize_land(v___x_157_, v___x_160_);
v___x_162_ = lean_array_uget_borrowed(v_buckets_148_, v___x_161_);
v___x_163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_147_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object* v_m_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_164_, v_a_165_);
lean_dec_ref(v_a_165_);
lean_dec_ref(v_m_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
return v_x_168_;
}
else
{
lean_object* v_key_170_; lean_object* v_value_171_; lean_object* v_tail_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_195_; 
v_key_170_ = lean_ctor_get(v_x_169_, 0);
v_value_171_ = lean_ctor_get(v_x_169_, 1);
v_tail_172_ = lean_ctor_get(v_x_169_, 2);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_195_ == 0)
{
v___x_174_ = v_x_169_;
v_isShared_175_ = v_isSharedCheck_195_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_tail_172_);
lean_inc(v_value_171_);
lean_inc(v_key_170_);
lean_dec(v_x_169_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_195_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v_fold_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_176_ = lean_array_get_size(v_x_168_);
v___x_177_ = l_Lean_Expr_hash(v_key_170_);
v___x_178_ = 32ULL;
v___x_179_ = lean_uint64_shift_right(v___x_177_, v___x_178_);
v_fold_180_ = lean_uint64_xor(v___x_177_, v___x_179_);
v___x_181_ = 16ULL;
v___x_182_ = lean_uint64_shift_right(v_fold_180_, v___x_181_);
v___x_183_ = lean_uint64_xor(v_fold_180_, v___x_182_);
v___x_184_ = lean_uint64_to_usize(v___x_183_);
v___x_185_ = lean_usize_of_nat(v___x_176_);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_sub(v___x_185_, v___x_186_);
v___x_188_ = lean_usize_land(v___x_184_, v___x_187_);
v___x_189_ = lean_array_uget_borrowed(v_x_168_, v___x_188_);
lean_inc(v___x_189_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 2, v___x_189_);
v___x_191_ = v___x_174_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_key_170_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_value_171_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___x_189_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = lean_array_uset(v_x_168_, v___x_188_, v___x_191_);
v_x_168_ = v___x_192_;
v_x_169_ = v_tail_172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_196_, lean_object* v_source_197_, lean_object* v_target_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_source_197_);
v___x_200_ = lean_nat_dec_lt(v_i_196_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec_ref(v_source_197_);
lean_dec(v_i_196_);
return v_target_198_;
}
else
{
lean_object* v_es_201_; lean_object* v___x_202_; lean_object* v_source_203_; lean_object* v_target_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_es_201_ = lean_array_fget(v_source_197_, v_i_196_);
v___x_202_ = lean_box(0);
v_source_203_ = lean_array_fset(v_source_197_, v_i_196_, v___x_202_);
v_target_204_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_198_, v_es_201_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_i_196_, v___x_205_);
lean_dec(v_i_196_);
v_i_196_ = v___x_206_;
v_source_197_ = v_source_203_;
v_target_198_ = v_target_204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object* v_data_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_nbuckets_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_209_ = lean_array_get_size(v_data_208_);
v___x_210_ = lean_unsigned_to_nat(2u);
v_nbuckets_211_ = lean_nat_mul(v___x_209_, v___x_210_);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_box(0);
v___x_214_ = lean_mk_array(v_nbuckets_211_, v___x_213_);
v___x_215_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v___x_212_, v_data_208_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object* v_m_216_, lean_object* v_a_217_, lean_object* v_b_218_){
_start:
{
lean_object* v_size_219_; lean_object* v_buckets_220_; lean_object* v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v_fold_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v_bkt_234_; uint8_t v___x_235_; 
v_size_219_ = lean_ctor_get(v_m_216_, 0);
v_buckets_220_ = lean_ctor_get(v_m_216_, 1);
v___x_221_ = lean_array_get_size(v_buckets_220_);
v___x_222_ = l_Lean_Expr_hash(v_a_217_);
v___x_223_ = 32ULL;
v___x_224_ = lean_uint64_shift_right(v___x_222_, v___x_223_);
v_fold_225_ = lean_uint64_xor(v___x_222_, v___x_224_);
v___x_226_ = 16ULL;
v___x_227_ = lean_uint64_shift_right(v_fold_225_, v___x_226_);
v___x_228_ = lean_uint64_xor(v_fold_225_, v___x_227_);
v___x_229_ = lean_uint64_to_usize(v___x_228_);
v___x_230_ = lean_usize_of_nat(v___x_221_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_sub(v___x_230_, v___x_231_);
v___x_233_ = lean_usize_land(v___x_229_, v___x_232_);
v_bkt_234_ = lean_array_uget_borrowed(v_buckets_220_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_217_, v_bkt_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_buckets_220_);
lean_inc(v_size_219_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_m_216_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_257_ = lean_ctor_get(v_m_216_, 1);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_m_216_, 0);
lean_dec(v_unused_258_);
v___x_237_ = v_m_216_;
v_isShared_238_ = v_isSharedCheck_256_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_m_216_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_256_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v_size_x27_240_; lean_object* v___x_241_; lean_object* v_buckets_x27_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v_size_x27_240_ = lean_nat_add(v_size_219_, v___x_239_);
lean_dec(v_size_219_);
lean_inc(v_bkt_234_);
v___x_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_241_, 0, v_a_217_);
lean_ctor_set(v___x_241_, 1, v_b_218_);
lean_ctor_set(v___x_241_, 2, v_bkt_234_);
v_buckets_x27_242_ = lean_array_uset(v_buckets_220_, v___x_233_, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(4u);
v___x_244_ = lean_nat_mul(v_size_x27_240_, v___x_243_);
v___x_245_ = lean_unsigned_to_nat(3u);
v___x_246_ = lean_nat_div(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_array_get_size(v_buckets_x27_242_);
v___x_248_ = lean_nat_dec_le(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
if (v___x_248_ == 0)
{
lean_object* v_val_249_; lean_object* v___x_251_; 
v_val_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_buckets_x27_242_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_249_);
lean_ctor_set(v___x_237_, 0, v_size_x27_240_);
v___x_251_ = v___x_237_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_size_x27_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_val_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_254_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_buckets_x27_242_);
lean_ctor_set(v___x_237_, 0, v_size_x27_240_);
v___x_254_ = v___x_237_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_size_x27_240_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_buckets_x27_242_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_dec(v_b_218_);
lean_dec_ref(v_a_217_);
return v_m_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_d_268_; lean_object* v_b_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; 
switch(lean_obj_tag(v_e_260_))
{
case 2:
{
lean_object* v_mvarId_289_; lean_object* v___x_290_; 
v_mvarId_289_ = lean_ctor_get(v_e_260_, 0);
lean_inc(v_mvarId_289_);
lean_dec_ref(v_e_260_);
v___x_290_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_289_, v_a_263_);
return v___x_290_;
}
case 3:
{
lean_object* v_u_291_; lean_object* v___x_292_; 
v_u_291_ = lean_ctor_get(v_e_260_, 0);
lean_inc(v_u_291_);
lean_dec_ref(v_e_260_);
v___x_292_ = l_Lean_Meta_hasAssignableLevelMVar(v_u_291_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_292_;
}
case 4:
{
lean_object* v_us_293_; lean_object* v___x_294_; 
v_us_293_ = lean_ctor_get(v_e_260_, 1);
lean_inc(v_us_293_);
lean_dec_ref(v_e_260_);
v___x_294_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_us_293_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_294_;
}
case 5:
{
lean_object* v_fn_295_; lean_object* v_arg_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_fn_295_ = lean_ctor_get(v_e_260_, 0);
lean_inc_ref(v_fn_295_);
v_arg_296_ = lean_ctor_get(v_e_260_, 1);
lean_inc_ref(v_arg_296_);
lean_dec_ref(v_e_260_);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_298_ = l_Lean_Core_checkSystem(v___x_297_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v___x_298_);
v___x_299_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_fn_295_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; uint8_t v___x_301_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
v___x_301_ = lean_unbox(v_a_300_);
lean_dec(v_a_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_299_);
v___x_302_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_arg_296_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_302_;
}
else
{
lean_dec_ref(v_arg_296_);
return v___x_299_;
}
}
else
{
lean_dec_ref(v_arg_296_);
return v___x_299_;
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_arg_296_);
lean_dec_ref(v_fn_295_);
v_a_303_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_298_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
case 6:
{
lean_object* v_binderType_311_; lean_object* v_body_312_; 
v_binderType_311_ = lean_ctor_get(v_e_260_, 1);
lean_inc_ref(v_binderType_311_);
v_body_312_ = lean_ctor_get(v_e_260_, 2);
lean_inc_ref(v_body_312_);
lean_dec_ref(v_e_260_);
v_d_268_ = v_binderType_311_;
v_b_269_ = v_body_312_;
v___y_270_ = v_a_261_;
v___y_271_ = v_a_262_;
v___y_272_ = v_a_263_;
v___y_273_ = v_a_264_;
v___y_274_ = v_a_265_;
goto v___jp_267_;
}
case 7:
{
lean_object* v_binderType_313_; lean_object* v_body_314_; 
v_binderType_313_ = lean_ctor_get(v_e_260_, 1);
lean_inc_ref(v_binderType_313_);
v_body_314_ = lean_ctor_get(v_e_260_, 2);
lean_inc_ref(v_body_314_);
lean_dec_ref(v_e_260_);
v_d_268_ = v_binderType_313_;
v_b_269_ = v_body_314_;
v___y_270_ = v_a_261_;
v___y_271_ = v_a_262_;
v___y_272_ = v_a_263_;
v___y_273_ = v_a_264_;
v___y_274_ = v_a_265_;
goto v___jp_267_;
}
case 8:
{
lean_object* v_type_315_; lean_object* v_value_316_; lean_object* v_body_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_type_315_ = lean_ctor_get(v_e_260_, 1);
lean_inc_ref(v_type_315_);
v_value_316_ = lean_ctor_get(v_e_260_, 2);
lean_inc_ref(v_value_316_);
v_body_317_ = lean_ctor_get(v_e_260_, 3);
lean_inc_ref(v_body_317_);
lean_dec_ref(v_e_260_);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_319_ = l_Lean_Core_checkSystem(v___x_318_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v___x_319_);
v___x_320_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_type_315_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; uint8_t v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
v___x_322_ = lean_unbox(v_a_321_);
lean_dec(v_a_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_320_);
v___x_323_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_value_316_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; uint8_t v___x_325_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
v___x_325_ = lean_unbox(v_a_324_);
lean_dec(v_a_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v___x_323_);
v___x_326_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_body_317_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_326_;
}
else
{
lean_dec_ref(v_body_317_);
return v___x_323_;
}
}
else
{
lean_dec_ref(v_body_317_);
return v___x_323_;
}
}
else
{
lean_dec_ref(v_body_317_);
lean_dec_ref(v_value_316_);
return v___x_320_;
}
}
else
{
lean_dec_ref(v_body_317_);
lean_dec_ref(v_value_316_);
return v___x_320_;
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_body_317_);
lean_dec_ref(v_value_316_);
lean_dec_ref(v_type_315_);
v_a_327_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_319_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_319_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
case 10:
{
lean_object* v_expr_335_; lean_object* v___x_336_; 
v_expr_335_ = lean_ctor_get(v_e_260_, 1);
lean_inc_ref(v_expr_335_);
lean_dec_ref(v_e_260_);
v___x_336_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_expr_335_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_336_;
}
case 11:
{
lean_object* v_struct_337_; lean_object* v___x_338_; 
v_struct_337_ = lean_ctor_get(v_e_260_, 2);
lean_inc_ref(v_struct_337_);
lean_dec_ref(v_e_260_);
v___x_338_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_struct_337_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_338_;
}
default: 
{
uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_e_260_);
v___x_339_ = 0;
v___x_340_ = lean_box(v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
v___jp_267_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_276_ = l_Lean_Core_checkSystem(v___x_275_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v___x_276_);
v___x_277_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_d_268_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; uint8_t v___x_279_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
v___x_279_ = lean_unbox(v_a_278_);
lean_dec(v_a_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v___x_277_);
v___x_280_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_b_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_280_;
}
else
{
lean_dec_ref(v_b_269_);
return v___x_277_;
}
}
else
{
lean_dec_ref(v_b_269_);
return v___x_277_;
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_b_269_);
lean_dec_ref(v_d_268_);
v_a_281_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_276_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_276_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Lean_Expr_hasMVar(v_e_342_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec_ref(v_e_342_);
v___x_350_ = lean_box(v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_st_ref_get(v_a_343_);
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v___x_352_, v_e_342_);
lean_dec(v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_st_ref_take(v_a_343_);
v___x_355_ = lean_box(0);
lean_inc_ref(v_e_342_);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_354_, v_e_342_, v___x_355_);
v___x_357_ = lean_st_ref_set(v_a_343_, v___x_356_);
v___x_358_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
return v___x_358_;
}
else
{
uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_e_342_);
v___x_359_ = 0;
v___x_360_ = lean_box(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object* v_e_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_378_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
return v_res_393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object* v_00_u03b2_394_, lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_395_, v_a_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object* v_00_u03b2_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(v_00_u03b2_398_, v_m_399_, v_a_400_);
lean_dec_ref(v_a_400_);
lean_dec_ref(v_m_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object* v_00_u03b2_403_, lean_object* v_m_404_, lean_object* v_a_405_, lean_object* v_b_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_404_, v_a_405_, v_b_406_);
return v___x_407_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object* v_00_u03b2_408_, lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_409_, v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_412_, lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(v_00_u03b2_412_, v_a_413_, v_x_414_);
lean_dec(v_x_414_);
lean_dec_ref(v_a_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object* v_00_u03b2_417_, lean_object* v_data_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_data_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_420_, lean_object* v_i_421_, lean_object* v_source_422_, lean_object* v_target_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v_i_421_, v_source_422_, v_target_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_426_, v_x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_unsigned_to_nat(16u);
v___x_431_ = lean_mk_array(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__0, &l_Lean_Meta_hasAssignableMVar___closed__0_once, _init_l_Lean_Meta_hasAssignableMVar___closed__0);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Expr_hasMVar(v_e_435_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v_e_435_);
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__1, &l_Lean_Meta_hasAssignableMVar___closed__1_once, _init_l_Lean_Meta_hasAssignableMVar___closed__1);
v___x_445_ = lean_st_mk_ref(v___x_444_);
v___x_446_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_435_, v___x_445_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_st_ref_get(v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_451_);
if (v_isShared_450_ == 0)
{
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_447_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_dec(v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_hasAssignableMVar(v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_462_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
