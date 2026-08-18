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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "hasAssignableMVar"};
static const lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_hasAssignableMVar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_hasAssignableMVar___closed__0;
static lean_once_cell_t l_Lean_Meta_hasAssignableMVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_hasAssignableMVar___closed__1;
static lean_once_cell_t l_Lean_Meta_hasAssignableMVar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_hasAssignableMVar___closed__2;
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
lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; uint8_t v_a_43_; lean_object* v_lvl_u2081_49_; lean_object* v_lvl_u2082_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; 
switch(lean_obj_tag(v_x_30_))
{
case 1:
{
lean_object* v_a_61_; uint8_t v___x_62_; 
v_a_61_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v_x_30_, 1);
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
lean_dec_ref_known(v_x_30_, 2);
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
lean_dec_ref_known(v_x_30_, 2);
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
lean_dec_ref_known(v_x_30_, 1);
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
v___x_44_ = l_Lean_Level_hasMVar(v___y_40_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v___y_40_);
v___x_45_ = lean_box(v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
else
{
v_x_30_ = v___y_40_;
v_a_31_ = v___y_39_;
v_a_32_ = v___y_37_;
v_a_33_ = v___y_41_;
v_a_34_ = v___y_38_;
goto _start;
}
}
else
{
lean_dec(v___y_40_);
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
v___y_38_ = v___y_54_;
v___y_39_ = v___y_51_;
v___y_40_ = v_lvl_u2082_50_;
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
v___y_38_ = v___y_54_;
v___y_39_ = v___y_51_;
v___y_40_ = v_lvl_u2082_50_;
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
lean_inc_ref(v_mctx_86_);
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
lean_dec_ref_known(v_x_113_, 2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object* v_m_135_, lean_object* v_query_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_x_138_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_dec(v_x_139_);
lean_dec(v_x_138_);
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(2);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_val_143_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v_x_137_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v_x_137_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_val_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_keyArray_151_; lean_object* v_valueArray_152_; lean_object* v___x_153_; uint8_t v_isSome_154_; 
v_keyArray_151_ = lean_ctor_get(v_m_135_, 1);
v_valueArray_152_ = lean_ctor_get(v_m_135_, 2);
v___x_153_ = lean_array_fget_borrowed(v_keyArray_151_, v_x_139_);
v_isSome_154_ = lean_noption_is_some(v___x_153_);
if (v_isSome_154_ == 0)
{
lean_dec(v_x_138_);
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_x_139_);
return v___x_155_;
}
else
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_x_139_);
v_val_156_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v_x_137_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_x_137_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_val_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_one_164_; lean_object* v_n_165_; lean_object* v___y_167_; 
v_one_164_ = lean_unsigned_to_nat(1u);
v_n_165_ = lean_nat_sub(v_x_138_, v_one_164_);
lean_dec(v_x_138_);
if (v_isSome_154_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v___x_175_; uint8_t v_isSome_176_; 
v___x_175_ = lean_array_fget_borrowed(v_valueArray_152_, v_x_139_);
v_isSome_176_ = lean_noption_is_some(v___x_175_);
if (v_isSome_176_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v_val_177_; uint8_t v___x_178_; 
lean_inc(v___x_153_);
v_val_177_ = lean_noption_get(v___x_153_);
v___x_178_ = lean_expr_eqv(v_val_177_, v_query_136_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
lean_dec(v_val_177_);
v___x_179_ = lean_array_get_size(v_keyArray_151_);
v___x_180_ = lean_nat_add(v_x_139_, v_one_164_);
lean_dec(v_x_139_);
v___x_181_ = lean_nat_dec_lt(v___x_180_, v___x_179_);
if (v___x_181_ == 0)
{
lean_dec(v___x_180_);
v_x_138_ = v_n_165_;
v_x_139_ = v_zero_140_;
goto _start;
}
else
{
v_x_138_ = v_n_165_;
v_x_139_ = v___x_180_;
goto _start;
}
}
else
{
lean_object* v_val_184_; lean_object* v___x_185_; 
lean_dec(v_n_165_);
lean_dec(v_x_137_);
lean_inc(v___x_175_);
v_val_184_ = lean_noption_get(v___x_175_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_x_139_);
lean_ctor_set(v___x_185_, 1, v_val_177_);
lean_ctor_set(v___x_185_, 2, v_val_184_);
return v___x_185_;
}
}
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_array_get_size(v_keyArray_151_);
v___x_169_ = lean_nat_add(v_x_139_, v_one_164_);
lean_dec(v_x_139_);
v___x_170_ = lean_nat_dec_lt(v___x_169_, v___x_168_);
if (v___x_170_ == 0)
{
lean_dec(v___x_169_);
v_x_137_ = v___y_167_;
v_x_138_ = v_n_165_;
v_x_139_ = v_zero_140_;
goto _start;
}
else
{
v_x_137_ = v___y_167_;
v_x_138_ = v_n_165_;
v_x_139_ = v___x_169_;
goto _start;
}
}
v___jp_173_:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_174_; 
lean_inc(v_x_139_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_x_139_);
v___y_167_ = v___x_174_;
goto v___jp_166_;
}
else
{
v___y_167_ = v_x_137_;
goto v___jp_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg___boxed(lean_object* v_m_186_, lean_object* v_query_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_m_186_, v_query_187_, v_x_188_, v_x_189_, v_x_190_);
lean_dec_ref(v_query_187_);
lean_dec_ref(v_m_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object* v_m_192_, lean_object* v_query_193_){
_start:
{
lean_object* v_keyArray_194_; lean_object* v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v_fold_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_keyArray_194_ = lean_ctor_get(v_m_192_, 1);
v___x_195_ = lean_array_get_size(v_keyArray_194_);
v___x_196_ = l_Lean_Expr_hash(v_query_193_);
v___x_197_ = 32ULL;
v___x_198_ = lean_uint64_shift_right(v___x_196_, v___x_197_);
v_fold_199_ = lean_uint64_xor(v___x_196_, v___x_198_);
v___x_200_ = 16ULL;
v___x_201_ = lean_uint64_shift_right(v_fold_199_, v___x_200_);
v___x_202_ = lean_uint64_xor(v_fold_199_, v___x_201_);
v___x_203_ = lean_uint64_to_usize(v___x_202_);
v___x_204_ = lean_usize_of_nat(v___x_195_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_sub(v___x_204_, v___x_205_);
v___x_207_ = lean_usize_land(v___x_203_, v___x_206_);
v___x_208_ = lean_usize_to_nat(v___x_207_);
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_m_192_, v_query_193_, v___x_209_, v___x_195_, v___x_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg___boxed(lean_object* v_m_211_, lean_object* v_query_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_211_, v_query_212_);
lean_dec_ref(v_query_212_);
lean_dec_ref(v_m_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object* v_m_214_, lean_object* v_query_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_214_, v_query_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_index_217_; lean_object* v_key_218_; lean_object* v_value_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
v_key_218_ = lean_ctor_get(v___x_216_, 1);
v_value_219_ = lean_ctor_get(v___x_216_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_216_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_value_219_);
lean_inc(v_key_218_);
lean_inc(v_index_217_);
lean_dec(v___x_216_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_index_217_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_key_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_value_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v___x_227_; 
lean_dec(v___x_216_);
v___x_227_ = lean_box(1);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object* v_m_228_, lean_object* v_query_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_m_228_, v_query_229_);
lean_dec_ref(v_query_229_);
lean_dec_ref(v_m_228_);
return v_res_230_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_m_231_, v_a_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
uint8_t v___x_234_; 
lean_dec_ref_known(v___x_233_, 3);
v___x_234_ = 1;
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_236_, v_a_237_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_m_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg(lean_object* v_b_240_, lean_object* v_acc_241_, lean_object* v_i_242_){
_start:
{
lean_object* v___y_244_; lean_object* v_keyArray_252_; lean_object* v_valueArray_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_keyArray_252_ = lean_ctor_get(v_b_240_, 1);
v_valueArray_253_ = lean_ctor_get(v_b_240_, 2);
v___x_254_ = lean_array_get_size(v_keyArray_252_);
v___x_255_ = lean_nat_dec_lt(v_i_242_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v_i_242_);
return v_acc_241_;
}
else
{
lean_object* v___x_256_; uint8_t v_isSome_257_; 
v___x_256_ = lean_array_fget_borrowed(v_keyArray_252_, v_i_242_);
v_isSome_257_ = lean_noption_is_some(v___x_256_);
if (v_isSome_257_ == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v___x_258_; uint8_t v_isSome_259_; 
v___x_258_ = lean_array_fget_borrowed(v_valueArray_253_, v_i_242_);
v_isSome_259_ = lean_noption_is_some(v___x_258_);
if (v_isSome_259_ == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v_val_260_; lean_object* v_val_261_; lean_object* v_i_263_; lean_object* v___x_268_; 
lean_inc(v___x_256_);
v_val_260_ = lean_noption_get(v___x_256_);
lean_inc(v___x_258_);
v_val_261_ = lean_noption_get(v___x_258_);
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_acc_241_, v_val_260_);
switch(lean_obj_tag(v___x_268_))
{
case 0:
{
lean_object* v_index_269_; lean_object* v_size_270_; lean_object* v___x_271_; 
v_index_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_index_269_);
lean_dec_ref_known(v___x_268_, 3);
v_size_270_ = lean_ctor_get(v_acc_241_, 0);
lean_inc(v_size_270_);
v___x_271_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_241_, v_size_270_, v_index_269_, v_val_260_, v_val_261_);
lean_dec(v_index_269_);
v___y_244_ = v___x_271_;
goto v___jp_243_;
}
case 1:
{
lean_object* v_index_272_; 
v_index_272_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_index_272_);
lean_dec_ref_known(v___x_268_, 1);
v_i_263_ = v_index_272_;
goto v___jp_262_;
}
default: 
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_241_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_index_275_; 
v_index_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_index_275_);
lean_dec_ref_known(v___x_274_, 1);
v_i_263_ = v_index_275_;
goto v___jp_262_;
}
else
{
lean_dec(v_val_261_);
lean_dec(v_val_260_);
v___y_244_ = v_acc_241_;
goto v___jp_243_;
}
}
}
v___jp_262_:
{
lean_object* v_size_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_size_264_ = lean_ctor_get(v_acc_241_, 0);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_size_264_, v___x_265_);
v___x_267_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_241_, v___x_266_, v_i_263_, v_val_260_, v_val_261_);
lean_dec(v_i_263_);
v___y_244_ = v___x_267_;
goto v___jp_243_;
}
}
}
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_i_242_, v___x_245_);
lean_dec(v_i_242_);
v_acc_241_ = v___y_244_;
v_i_242_ = v___x_246_;
goto _start;
}
v___jp_248_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_i_242_, v___x_249_);
lean_dec(v_i_242_);
v_i_242_ = v___x_250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_b_276_, lean_object* v_acc_277_, lean_object* v_i_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg(v_b_276_, v_acc_277_, v_i_278_);
lean_dec_ref(v_b_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg(lean_object* v_init_280_, lean_object* v_b_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg(v_b_281_, v_init_280_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg___boxed(lean_object* v_init_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg(v_init_284_, v_b_285_);
lean_dec_ref(v_b_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(lean_object* v_m_287_){
_start:
{
lean_object* v_keyArray_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_cellCount_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_target_295_; lean_object* v___x_296_; 
v_keyArray_288_ = lean_ctor_get(v_m_287_, 1);
v___x_289_ = lean_array_get_size(v_keyArray_288_);
v___x_290_ = lean_unsigned_to_nat(2u);
v_cellCount_291_ = lean_nat_mul(v___x_289_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_291_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_291_);
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_291_);
v_target_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_295_, 0, v___x_292_);
lean_ctor_set(v_target_295_, 1, v___x_293_);
lean_ctor_set(v_target_295_, 2, v___x_294_);
v___x_296_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg(v_target_295_, v_m_287_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg___boxed(lean_object* v_m_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(v_m_297_);
lean_dec_ref(v_m_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_Expr_hasMVar(v_e_300_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref(v_e_300_);
v___x_308_ = lean_box(v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_st_ref_get(v_a_301_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v___x_310_, v_e_300_);
lean_dec(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___y_314_; lean_object* v___x_317_; lean_object* v___y_319_; lean_object* v_i_320_; lean_object* v___y_326_; lean_object* v___y_336_; lean_object* v_i_337_; lean_object* v___x_352_; 
v___x_312_ = lean_st_ref_take(v_a_301_);
v___x_317_ = lean_box(0);
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_312_, v_e_300_);
switch(lean_obj_tag(v___x_352_))
{
case 0:
{
lean_dec_ref_known(v___x_352_, 3);
v___y_314_ = v___x_312_;
goto v___jp_313_;
}
case 1:
{
lean_object* v_index_353_; lean_object* v_size_354_; lean_object* v_keyArray_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_index_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_index_353_);
lean_dec_ref_known(v___x_352_, 1);
v_size_354_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_size_354_);
v_keyArray_355_ = lean_ctor_get(v___x_312_, 1);
lean_inc_ref(v_keyArray_355_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_size_354_, v___x_356_);
lean_dec(v_size_354_);
v___x_358_ = lean_array_get_size(v_keyArray_355_);
lean_dec_ref(v_keyArray_355_);
v___x_359_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_dec(v___x_357_);
lean_dec(v_index_353_);
goto v___jp_342_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_mul(v___x_357_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_nat_mul(v___x_358_, v___x_362_);
v___x_364_ = lean_nat_dec_le(v___x_361_, v___x_363_);
lean_dec(v___x_363_);
lean_dec(v___x_361_);
if (v___x_364_ == 0)
{
lean_dec(v___x_357_);
lean_dec(v_index_353_);
goto v___jp_342_;
}
else
{
lean_object* v___x_365_; 
lean_inc_ref(v_e_300_);
v___x_365_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_312_, v___x_357_, v_index_353_, v_e_300_, v___x_317_);
lean_dec(v_index_353_);
v___y_314_ = v___x_365_;
goto v___jp_313_;
}
}
}
default: 
{
lean_object* v_size_366_; lean_object* v_keyArray_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_size_366_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_size_366_);
v_keyArray_367_ = lean_ctor_get(v___x_312_, 1);
lean_inc_ref(v_keyArray_367_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_size_366_, v___x_368_);
lean_dec(v_size_366_);
v___x_370_ = lean_array_get_size(v_keyArray_367_);
lean_dec_ref(v_keyArray_367_);
v___x_371_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v___x_369_);
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(v___x_312_);
lean_dec(v___x_312_);
v___y_326_ = v___x_372_;
goto v___jp_325_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_373_ = lean_unsigned_to_nat(4u);
v___x_374_ = lean_nat_mul(v___x_369_, v___x_373_);
lean_dec(v___x_369_);
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = lean_nat_mul(v___x_370_, v___x_375_);
v___x_377_ = lean_nat_dec_le(v___x_374_, v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_374_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(v___x_312_);
lean_dec(v___x_312_);
v___y_326_ = v___x_378_;
goto v___jp_325_;
}
else
{
v___y_326_ = v___x_312_;
goto v___jp_325_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_st_ref_put(v_a_301_, v___y_314_);
v___x_316_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
return v___x_316_;
}
v___jp_318_:
{
lean_object* v_size_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_size_321_ = lean_ctor_get(v___y_319_, 0);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_size_321_, v___x_322_);
lean_inc_ref(v_e_300_);
v___x_324_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_319_, v___x_323_, v_i_320_, v_e_300_, v___x_317_);
lean_dec(v_i_320_);
v___y_314_ = v___x_324_;
goto v___jp_313_;
}
v___jp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___y_326_, v_e_300_);
switch(lean_obj_tag(v___x_327_))
{
case 0:
{
lean_object* v_index_328_; lean_object* v_size_329_; lean_object* v___x_330_; 
v_index_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_index_328_);
lean_dec_ref_known(v___x_327_, 3);
v_size_329_ = lean_ctor_get(v___y_326_, 0);
lean_inc(v_size_329_);
lean_inc_ref(v_e_300_);
v___x_330_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_326_, v_size_329_, v_index_328_, v_e_300_, v___x_317_);
lean_dec(v_index_328_);
v___y_314_ = v___x_330_;
goto v___jp_313_;
}
case 1:
{
lean_object* v_index_331_; 
v_index_331_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_index_331_);
lean_dec_ref_known(v___x_327_, 1);
v___y_319_ = v___y_326_;
v_i_320_ = v_index_331_;
goto v___jp_318_;
}
default: 
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_326_, v___x_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_index_334_; 
v_index_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_index_334_);
lean_dec_ref_known(v___x_333_, 1);
v___y_319_ = v___y_326_;
v_i_320_ = v_index_334_;
goto v___jp_318_;
}
else
{
v___y_314_ = v___y_326_;
goto v___jp_313_;
}
}
}
}
v___jp_335_:
{
lean_object* v_size_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_size_338_ = lean_ctor_get(v___y_336_, 0);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_size_338_, v___x_339_);
lean_inc_ref(v_e_300_);
v___x_341_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_336_, v___x_340_, v_i_337_, v_e_300_, v___x_317_);
lean_dec(v_i_337_);
v___y_314_ = v___x_341_;
goto v___jp_313_;
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(v___x_312_);
lean_dec(v___x_312_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_343_, v_e_300_);
switch(lean_obj_tag(v___x_344_))
{
case 0:
{
lean_object* v_index_345_; lean_object* v_size_346_; lean_object* v___x_347_; 
v_index_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_345_);
lean_dec_ref_known(v___x_344_, 3);
v_size_346_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_size_346_);
lean_inc_ref(v_e_300_);
v___x_347_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_343_, v_size_346_, v_index_345_, v_e_300_, v___x_317_);
lean_dec(v_index_345_);
v___y_314_ = v___x_347_;
goto v___jp_313_;
}
case 1:
{
lean_object* v_index_348_; 
v_index_348_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_344_, 1);
v___y_336_ = v___x_343_;
v_i_337_ = v_index_348_;
goto v___jp_335_;
}
default: 
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_343_, v___x_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_index_351_; 
v_index_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_index_351_);
lean_dec_ref_known(v___x_350_, 1);
v___y_336_ = v___x_343_;
v_i_337_ = v_index_351_;
goto v___jp_335_;
}
else
{
v___y_314_ = v___x_343_;
goto v___jp_313_;
}
}
}
}
}
else
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v_e_300_);
v___x_379_ = 0;
v___x_380_ = lean_box(v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object* v_e_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_d_390_; lean_object* v_b_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; 
switch(lean_obj_tag(v_e_382_))
{
case 2:
{
lean_object* v_mvarId_411_; lean_object* v___x_412_; 
v_mvarId_411_ = lean_ctor_get(v_e_382_, 0);
lean_inc(v_mvarId_411_);
lean_dec_ref_known(v_e_382_, 1);
v___x_412_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_411_, v_a_385_);
return v___x_412_;
}
case 3:
{
lean_object* v_u_413_; lean_object* v___x_414_; 
v_u_413_ = lean_ctor_get(v_e_382_, 0);
lean_inc(v_u_413_);
lean_dec_ref_known(v_e_382_, 1);
v___x_414_ = l_Lean_Meta_hasAssignableLevelMVar(v_u_413_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_414_;
}
case 4:
{
lean_object* v_us_415_; lean_object* v___x_416_; 
v_us_415_ = lean_ctor_get(v_e_382_, 1);
lean_inc(v_us_415_);
lean_dec_ref_known(v_e_382_, 2);
v___x_416_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_us_415_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_416_;
}
case 5:
{
lean_object* v_fn_417_; lean_object* v_arg_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_fn_417_ = lean_ctor_get(v_e_382_, 0);
lean_inc_ref(v_fn_417_);
v_arg_418_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_arg_418_);
lean_dec_ref_known(v_e_382_, 2);
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_420_ = l_Lean_Core_checkSystem(v___x_419_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; 
lean_dec_ref_known(v___x_420_, 1);
v___x_421_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_fn_417_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; uint8_t v___x_423_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
v___x_423_ = lean_unbox(v_a_422_);
lean_dec(v_a_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec_ref_known(v___x_421_, 1);
v___x_424_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_arg_418_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_424_;
}
else
{
lean_dec_ref(v_arg_418_);
return v___x_421_;
}
}
else
{
lean_dec_ref(v_arg_418_);
return v___x_421_;
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_arg_418_);
lean_dec_ref(v_fn_417_);
v_a_425_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_420_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_420_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
case 6:
{
lean_object* v_binderType_433_; lean_object* v_body_434_; 
v_binderType_433_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_binderType_433_);
v_body_434_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_body_434_);
lean_dec_ref_known(v_e_382_, 3);
v_d_390_ = v_binderType_433_;
v_b_391_ = v_body_434_;
v___y_392_ = v_a_383_;
v___y_393_ = v_a_384_;
v___y_394_ = v_a_385_;
v___y_395_ = v_a_386_;
v___y_396_ = v_a_387_;
goto v___jp_389_;
}
case 7:
{
lean_object* v_binderType_435_; lean_object* v_body_436_; 
v_binderType_435_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_binderType_435_);
v_body_436_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_body_436_);
lean_dec_ref_known(v_e_382_, 3);
v_d_390_ = v_binderType_435_;
v_b_391_ = v_body_436_;
v___y_392_ = v_a_383_;
v___y_393_ = v_a_384_;
v___y_394_ = v_a_385_;
v___y_395_ = v_a_386_;
v___y_396_ = v_a_387_;
goto v___jp_389_;
}
case 8:
{
lean_object* v_type_437_; lean_object* v_value_438_; lean_object* v_body_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_type_437_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_type_437_);
v_value_438_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_value_438_);
v_body_439_ = lean_ctor_get(v_e_382_, 3);
lean_inc_ref(v_body_439_);
lean_dec_ref_known(v_e_382_, 4);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_441_ = l_Lean_Core_checkSystem(v___x_440_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; 
lean_dec_ref_known(v___x_441_, 1);
v___x_442_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_type_437_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
v___x_444_ = lean_unbox(v_a_443_);
lean_dec(v_a_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec_ref_known(v___x_442_, 1);
v___x_445_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_value_438_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; uint8_t v___x_447_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
v___x_447_ = lean_unbox(v_a_446_);
lean_dec(v_a_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_448_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_body_439_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_448_;
}
else
{
lean_dec_ref(v_body_439_);
return v___x_445_;
}
}
else
{
lean_dec_ref(v_body_439_);
return v___x_445_;
}
}
else
{
lean_dec_ref(v_body_439_);
lean_dec_ref(v_value_438_);
return v___x_442_;
}
}
else
{
lean_dec_ref(v_body_439_);
lean_dec_ref(v_value_438_);
return v___x_442_;
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_body_439_);
lean_dec_ref(v_value_438_);
lean_dec_ref(v_type_437_);
v_a_449_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_441_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_441_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
case 10:
{
lean_object* v_expr_457_; lean_object* v___x_458_; 
v_expr_457_ = lean_ctor_get(v_e_382_, 1);
lean_inc_ref(v_expr_457_);
lean_dec_ref_known(v_e_382_, 2);
v___x_458_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_expr_457_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_458_;
}
case 11:
{
lean_object* v_struct_459_; lean_object* v___x_460_; 
v_struct_459_ = lean_ctor_get(v_e_382_, 2);
lean_inc_ref(v_struct_459_);
lean_dec_ref_known(v_e_382_, 3);
v___x_460_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_struct_459_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_460_;
}
default: 
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v_e_382_);
v___x_461_ = 0;
v___x_462_ = lean_box(v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
v___jp_389_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_398_ = l_Lean_Core_checkSystem(v___x_397_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_d_390_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; uint8_t v___x_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
v___x_401_ = lean_unbox(v_a_400_);
lean_dec(v_a_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_402_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_b_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v___x_402_;
}
else
{
lean_dec_ref(v_b_391_);
return v___x_399_;
}
}
else
{
lean_dec_ref(v_b_391_);
return v___x_399_;
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_b_391_);
lean_dec_ref(v_d_390_);
v_a_403_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_398_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_398_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object* v_e_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_e_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_480_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
return v_res_495_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(v_00_u03b2_500_, v_m_501_, v_a_502_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_m_501_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object* v_00_u03b2_505_, lean_object* v_m_506_, lean_object* v_query_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_506_, v_query_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___boxed(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_query_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(v_00_u03b2_509_, v_m_510_, v_query_511_);
lean_dec_ref(v_query_511_);
lean_dec_ref(v_m_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5(lean_object* v_00_u03b2_513_, lean_object* v_m_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___redArg(v_m_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5___boxed(lean_object* v_00_u03b2_516_, lean_object* v_m_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5(v_00_u03b2_516_, v_m_517_);
lean_dec_ref(v_m_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object* v_00_u03b2_519_, lean_object* v_m_520_, lean_object* v_query_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_m_520_, v_query_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_523_, lean_object* v_m_524_, lean_object* v_query_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(v_00_u03b2_523_, v_m_524_, v_query_525_);
lean_dec_ref(v_query_525_);
lean_dec_ref(v_m_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object* v_00_u03b2_527_, lean_object* v_m_528_, lean_object* v_query_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_m_528_, v_query_529_, v_x_530_, v_x_531_, v_x_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_535_, lean_object* v_m_536_, lean_object* v_query_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(v_00_u03b2_535_, v_m_536_, v_query_537_, v_x_538_, v_x_539_, v_x_540_, v_x_541_);
lean_dec_ref(v_query_537_);
lean_dec_ref(v_m_536_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7(lean_object* v_00_u03b2_543_, lean_object* v_init_544_, lean_object* v_b_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___redArg(v_init_544_, v_b_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7___boxed(lean_object* v_00_u03b2_547_, lean_object* v_init_548_, lean_object* v_b_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7(v_00_u03b2_547_, v_init_548_, v_b_549_);
lean_dec_ref(v_b_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_551_, lean_object* v_b_552_, lean_object* v_acc_553_, lean_object* v_i_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___redArg(v_b_552_, v_acc_553_, v_i_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8___boxed(lean_object* v_00_u03b2_556_, lean_object* v_b_557_, lean_object* v_acc_558_, lean_object* v_i_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__5_spec__7_spec__8(v_00_u03b2_556_, v_b_557_, v_acc_558_, v_i_559_);
lean_dec_ref(v_b_557_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__0(void){
_start:
{
lean_object* v_cellCount_561_; lean_object* v___x_562_; 
v_cellCount_561_ = lean_unsigned_to_nat(16u);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_561_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__1(void){
_start:
{
lean_object* v_cellCount_563_; lean_object* v___x_564_; 
v_cellCount_563_ = lean_unsigned_to_nat(16u);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__2(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__1, &l_Lean_Meta_hasAssignableMVar___closed__1_once, _init_l_Lean_Meta_hasAssignableMVar___closed__1);
v___x_566_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__0, &l_Lean_Meta_hasAssignableMVar___closed__0_once, _init_l_Lean_Meta_hasAssignableMVar___closed__0);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
lean_ctor_set(v___x_568_, 2, v___x_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = l_Lean_Expr_hasMVar(v_e_569_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_e_569_);
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__2, &l_Lean_Meta_hasAssignableMVar___closed__2_once, _init_l_Lean_Meta_hasAssignableMVar___closed__2);
v___x_579_ = lean_st_mk_ref(v___x_578_);
v___x_580_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_569_, v___x_579_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_st_ref_get(v___x_579_);
lean_dec(v___x_579_);
lean_dec(v___x_585_);
if (v_isShared_584_ == 0)
{
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_581_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_dec(v___x_579_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_hasAssignableMVar(v_e_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_596_;
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
