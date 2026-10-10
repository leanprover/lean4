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
lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_mvarId_1_, v___y_2_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg___boxed(lean_object* v_mvarId_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_mvarId_13_, v___y_14_);
lean_dec(v___y_14_);
return v_res_16_;
}
}
lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(lean_object* v_mvarId_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_mvarId_17_, v___y_19_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_17_ = stack[0].m_obj;
lean_object* v___y_18_ = stack[1].m_obj;
lean_object* v___y_19_ = stack[2].m_obj;
lean_object* v___y_20_ = stack[3].m_obj;
lean_object* v___y_21_ = stack[4].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(v_mvarId_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___boxed(lean_object* v_mvarId_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(v_mvarId_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
return v_res_31_;
}
}
lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_44_; uint8_t v_a_45_; lean_object* v_lvl_u2081_51_; lean_object* v_lvl_u2082_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; 
switch(lean_obj_tag(v_x_32_))
{
case 1:
{
lean_object* v_a_63_; uint8_t v___x_64_; 
v_a_63_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v_x_32_, 1);
v___x_64_ = l_Lean_Level_hasMVar(v_a_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_a_63_);
v___x_65_ = lean_box(v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
v_x_32_ = v_a_63_;
goto _start;
}
}
case 2:
{
lean_object* v_a_68_; lean_object* v_a_69_; 
v_a_68_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v_x_32_, 2);
v_lvl_u2081_51_ = v_a_68_;
v_lvl_u2082_52_ = v_a_69_;
v___y_53_ = v_a_33_;
v___y_54_ = v_a_34_;
v___y_55_ = v_a_35_;
v___y_56_ = v_a_36_;
goto v___jp_50_;
}
case 3:
{
lean_object* v_a_70_; lean_object* v_a_71_; 
v_a_70_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_70_);
v_a_71_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_a_71_);
lean_dec_ref_known(v_x_32_, 2);
v_lvl_u2081_51_ = v_a_70_;
v_lvl_u2082_52_ = v_a_71_;
v___y_53_ = v_a_33_;
v___y_54_ = v_a_34_;
v___y_55_ = v_a_35_;
v___y_56_ = v_a_36_;
goto v___jp_50_;
}
case 5:
{
lean_object* v_a_72_; lean_object* v___x_73_; 
v_a_72_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v_x_32_, 1);
v___x_73_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_a_72_, v_a_34_);
return v___x_73_;
}
default: 
{
uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_x_32_);
v___x_74_ = 0;
v___x_75_ = lean_box(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
v___jp_38_:
{
if (v_a_45_ == 0)
{
uint8_t v___x_46_; 
lean_dec_ref(v___y_44_);
v___x_46_ = l_Lean_Level_hasMVar(v___y_39_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v___y_39_);
v___x_47_ = lean_box(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
else
{
v_x_32_ = v___y_39_;
v_a_33_ = v___y_42_;
v_a_34_ = v___y_43_;
v_a_35_ = v___y_41_;
v_a_36_ = v___y_40_;
goto _start;
}
}
else
{
lean_dec(v___y_39_);
return v___y_44_;
}
}
v___jp_50_:
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_Level_hasMVar(v_lvl_u2081_51_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_lvl_u2081_51_);
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
v___y_39_ = v_lvl_u2082_52_;
v___y_40_ = v___y_56_;
v___y_41_ = v___y_55_;
v___y_42_ = v___y_53_;
v___y_43_ = v___y_54_;
v___y_44_ = v___x_59_;
v_a_45_ = v___x_57_;
goto v___jp_38_;
}
else
{
lean_object* v___x_60_; lean_object* v_a_61_; uint8_t v___x_62_; 
v___x_60_ = l_Lean_Meta_hasAssignableLevelMVar(v_lvl_u2081_51_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v___x_62_ = lean_unbox(v_a_61_);
v___y_39_ = v_lvl_u2082_52_;
v___y_40_ = v___y_56_;
v___y_41_ = v___y_55_;
v___y_42_ = v___y_53_;
v___y_43_ = v___y_54_;
v___y_44_ = v___x_60_;
v_a_45_ = v___x_62_;
goto v___jp_38_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_hasAssignableLevelMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_32_ = stack[0].m_obj;
lean_object* v_a_33_ = stack[1].m_obj;
lean_object* v_a_34_ = stack[2].m_obj;
lean_object* v_a_35_ = stack[3].m_obj;
lean_object* v_a_36_ = stack[4].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Lean_Meta_hasAssignableLevelMVar(v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableLevelMVar___boxed(lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_hasAssignableLevelMVar(v_x_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_84_;
}
}
lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(lean_object* v_mvarId_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v_mctx_89_; lean_object* v_decl_90_; lean_object* v_depth_91_; lean_object* v_depth_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_mctx_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_mctx_89_);
lean_dec(v___x_88_);
v_decl_90_ = l_Lean_MetavarContext_getDecl(v_mctx_89_, v_mvarId_85_);
v_depth_91_ = lean_ctor_get(v_decl_90_, 3);
lean_inc(v_depth_91_);
lean_dec_ref(v_decl_90_);
v_depth_92_ = lean_ctor_get(v_mctx_89_, 0);
lean_inc(v_depth_92_);
lean_dec_ref(v_mctx_89_);
v___x_93_ = lean_nat_dec_eq(v_depth_91_, v_depth_92_);
lean_dec(v_depth_92_);
lean_dec(v_depth_91_);
v___x_94_ = lean_box(v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_85_ = stack[0].m_obj;
lean_object* v___y_86_ = stack[1].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_85_, v___y_86_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg___boxed(lean_object* v_mvarId_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_97_, v___y_98_);
lean_dec(v___y_98_);
return v_res_100_;
}
}
lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(lean_object* v_mvarId_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_101_, v___y_104_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_101_ = stack[0].m_obj;
lean_object* v___y_102_ = stack[1].m_obj;
lean_object* v___y_103_ = stack[2].m_obj;
lean_object* v___y_104_ = stack[3].m_obj;
lean_object* v___y_105_ = stack[4].m_obj;
lean_object* v___y_106_ = stack[5].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(v_mvarId_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___boxed(lean_object* v_mvarId_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(v_mvarId_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
return v_res_117_;
}
}
lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(lean_object* v_x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = 0;
v___x_125_ = lean_box(v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_129_; lean_object* v_a_130_; uint8_t v___x_131_; 
v_head_127_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_head_127_);
v_tail_128_ = lean_ctor_get(v_x_118_, 1);
lean_inc(v_tail_128_);
lean_dec_ref_known(v_x_118_, 2);
v___x_129_ = l_Lean_Meta_hasAssignableLevelMVar(v_head_127_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v___x_131_ = lean_unbox(v_a_130_);
if (v___x_131_ == 0)
{
lean_dec_ref(v___x_129_);
v_x_118_ = v_tail_128_;
goto _start;
}
else
{
lean_dec(v_tail_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT void l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_118_ = stack[0].m_obj;
lean_object* v___y_119_ = stack[1].m_obj;
lean_object* v___y_120_ = stack[2].m_obj;
lean_object* v___y_121_ = stack[3].m_obj;
lean_object* v___y_122_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg___boxed(lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
else
{
lean_object* v_key_144_; lean_object* v_tail_145_; uint8_t v___x_146_; 
v_key_144_ = lean_ctor_get(v_x_142_, 0);
v_tail_145_ = lean_ctor_get(v_x_142_, 2);
v___x_146_ = lean_expr_eqv(v_key_144_, v_a_141_);
if (v___x_146_ == 0)
{
v_x_142_ = v_tail_145_;
goto _start;
}
else
{
return v___x_146_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_141_ = stack[0].m_obj;
lean_object* v_x_142_ = stack[1].m_obj;
uint8_t v_res_148_;
v_res_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_141_, v_x_142_);
stack->m_num = v_res_148_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_149_, v_x_150_);
lean_dec(v_x_150_);
lean_dec_ref(v_a_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(lean_object* v_m_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_buckets_155_; lean_object* v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v_fold_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_buckets_155_ = lean_ctor_get(v_m_153_, 1);
v___x_156_ = lean_array_get_size(v_buckets_155_);
v___x_157_ = l_Lean_Expr_hash(v_a_154_);
v___x_158_ = 32ULL;
v___x_159_ = lean_uint64_shift_right(v___x_157_, v___x_158_);
v_fold_160_ = lean_uint64_xor(v___x_157_, v___x_159_);
v___x_161_ = 16ULL;
v___x_162_ = lean_uint64_shift_right(v_fold_160_, v___x_161_);
v___x_163_ = lean_uint64_xor(v_fold_160_, v___x_162_);
v___x_164_ = lean_uint64_to_usize(v___x_163_);
v___x_165_ = lean_usize_of_nat(v___x_156_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_sub(v___x_165_, v___x_166_);
v___x_168_ = lean_usize_land(v___x_164_, v___x_167_);
v___x_169_ = lean_array_uget_borrowed(v_buckets_155_, v___x_168_);
v___x_170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_154_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_153_ = stack[0].m_obj;
lean_object* v_a_154_ = stack[1].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_153_, v_a_154_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(lean_object* v_m_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_172_, v_a_173_);
lean_dec_ref(v_a_173_);
lean_dec_ref(v_m_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
return v_x_176_;
}
else
{
lean_object* v_key_178_; lean_object* v_value_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_203_; 
v_key_178_ = lean_ctor_get(v_x_177_, 0);
v_value_179_ = lean_ctor_get(v_x_177_, 1);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_203_ == 0)
{
v___x_182_ = v_x_177_;
v_isShared_183_ = v_isSharedCheck_203_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_value_179_);
lean_inc(v_key_178_);
lean_dec(v_x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_203_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_184_ = lean_array_get_size(v_x_176_);
v___x_185_ = l_Lean_Expr_hash(v_key_178_);
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___x_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___x_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_184_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v___x_197_ = lean_array_uget_borrowed(v_x_176_, v___x_196_);
lean_inc(v___x_197_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 2, v___x_197_);
v___x_199_ = v___x_182_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_key_178_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_value_179_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___x_197_);
v___x_199_ = v_reuseFailAlloc_202_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_uset(v_x_176_, v___x_196_, v___x_199_);
v_x_176_ = v___x_200_;
v_x_177_ = v_tail_180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(lean_object* v_i_204_, lean_object* v_source_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_array_get_size(v_source_205_);
v___x_208_ = lean_nat_dec_lt(v_i_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v_source_205_);
lean_dec(v_i_204_);
return v_target_206_;
}
else
{
lean_object* v_es_209_; lean_object* v___x_210_; lean_object* v_source_211_; lean_object* v_target_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_es_209_ = lean_array_fget(v_source_205_, v_i_204_);
v___x_210_ = lean_box(0);
v_source_211_ = lean_array_fset(v_source_205_, v_i_204_, v___x_210_);
v_target_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_206_, v_es_209_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_i_204_, v___x_213_);
lean_dec(v_i_204_);
v_i_204_ = v___x_214_;
v_source_205_ = v_source_211_;
v_target_206_ = v_target_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(lean_object* v_data_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_nbuckets_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_217_ = lean_array_get_size(v_data_216_);
v___x_218_ = lean_unsigned_to_nat(2u);
v_nbuckets_219_ = lean_nat_mul(v___x_217_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_box(0);
v___x_222_ = lean_mk_array(v_nbuckets_219_, v___x_221_);
v___x_223_ = lean_array_propagate_mark(v_data_216_, v___x_222_);
v___x_224_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v___x_220_, v_data_216_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(lean_object* v_m_225_, lean_object* v_a_226_, lean_object* v_b_227_){
_start:
{
lean_object* v_size_228_; lean_object* v_buckets_229_; lean_object* v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v_fold_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v_bkt_243_; uint8_t v___x_244_; 
v_size_228_ = lean_ctor_get(v_m_225_, 0);
v_buckets_229_ = lean_ctor_get(v_m_225_, 1);
v___x_230_ = lean_array_get_size(v_buckets_229_);
v___x_231_ = l_Lean_Expr_hash(v_a_226_);
v___x_232_ = 32ULL;
v___x_233_ = lean_uint64_shift_right(v___x_231_, v___x_232_);
v_fold_234_ = lean_uint64_xor(v___x_231_, v___x_233_);
v___x_235_ = 16ULL;
v___x_236_ = lean_uint64_shift_right(v_fold_234_, v___x_235_);
v___x_237_ = lean_uint64_xor(v_fold_234_, v___x_236_);
v___x_238_ = lean_uint64_to_usize(v___x_237_);
v___x_239_ = lean_usize_of_nat(v___x_230_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_sub(v___x_239_, v___x_240_);
v___x_242_ = lean_usize_land(v___x_238_, v___x_241_);
v_bkt_243_ = lean_array_uget_borrowed(v_buckets_229_, v___x_242_);
v___x_244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_226_, v_bkt_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_265_; 
lean_inc_ref(v_buckets_229_);
lean_inc(v_size_228_);
v_isSharedCheck_265_ = !lean_is_exclusive(v_m_225_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_266_ = lean_ctor_get(v_m_225_, 1);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_m_225_, 0);
lean_dec(v_unused_267_);
v___x_246_ = v_m_225_;
v_isShared_247_ = v_isSharedCheck_265_;
goto v_resetjp_245_;
}
else
{
lean_dec(v_m_225_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_265_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v_size_x27_249_; lean_object* v___x_250_; lean_object* v_buckets_x27_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_248_ = lean_unsigned_to_nat(1u);
v_size_x27_249_ = lean_nat_add(v_size_228_, v___x_248_);
lean_dec(v_size_228_);
lean_inc(v_bkt_243_);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v_a_226_);
lean_ctor_set(v___x_250_, 1, v_b_227_);
lean_ctor_set(v___x_250_, 2, v_bkt_243_);
v_buckets_x27_251_ = lean_array_uset(v_buckets_229_, v___x_242_, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(4u);
v___x_253_ = lean_nat_mul(v_size_x27_249_, v___x_252_);
v___x_254_ = lean_unsigned_to_nat(3u);
v___x_255_ = lean_nat_div(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_array_get_size(v_buckets_x27_251_);
v___x_257_ = lean_nat_dec_le(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v_val_258_; lean_object* v___x_260_; 
v_val_258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_buckets_x27_251_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_val_258_);
lean_ctor_set(v___x_246_, 0, v_size_x27_249_);
v___x_260_ = v___x_246_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_size_x27_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_val_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v___x_263_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_buckets_x27_251_);
lean_ctor_set(v___x_246_, 0, v_size_x27_249_);
v___x_263_ = v___x_246_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_size_x27_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_buckets_x27_251_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_dec(v_b_227_);
lean_dec_ref(v_a_226_);
return v_m_225_;
}
}
}
lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(lean_object* v_e_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_d_277_; lean_object* v_b_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; 
switch(lean_obj_tag(v_e_269_))
{
case 2:
{
lean_object* v_mvarId_298_; lean_object* v___x_299_; 
v_mvarId_298_ = lean_ctor_get(v_e_269_, 0);
lean_inc(v_mvarId_298_);
lean_dec_ref_known(v_e_269_, 1);
v___x_299_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_298_, v_a_272_);
return v___x_299_;
}
case 3:
{
lean_object* v_u_300_; lean_object* v___x_301_; 
v_u_300_ = lean_ctor_get(v_e_269_, 0);
lean_inc(v_u_300_);
lean_dec_ref_known(v_e_269_, 1);
v___x_301_ = l_Lean_Meta_hasAssignableLevelMVar(v_u_300_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_301_;
}
case 4:
{
lean_object* v_us_302_; lean_object* v___x_303_; 
v_us_302_ = lean_ctor_get(v_e_269_, 1);
lean_inc(v_us_302_);
lean_dec_ref_known(v_e_269_, 2);
v___x_303_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_us_302_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_303_;
}
case 5:
{
lean_object* v_fn_304_; lean_object* v_arg_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_fn_304_ = lean_ctor_get(v_e_269_, 0);
lean_inc_ref(v_fn_304_);
v_arg_305_ = lean_ctor_get(v_e_269_, 1);
lean_inc_ref(v_arg_305_);
lean_dec_ref_known(v_e_269_, 2);
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_307_ = l_Lean_Core_checkSystem(v___x_306_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_fn_304_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; uint8_t v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v___x_310_ = lean_unbox(v_a_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_311_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_arg_305_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_311_;
}
else
{
lean_dec_ref(v_arg_305_);
return v___x_308_;
}
}
else
{
lean_dec_ref(v_arg_305_);
return v___x_308_;
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_fn_304_);
v_a_312_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
case 6:
{
lean_object* v_binderType_320_; lean_object* v_body_321_; 
v_binderType_320_ = lean_ctor_get(v_e_269_, 1);
lean_inc_ref(v_binderType_320_);
v_body_321_ = lean_ctor_get(v_e_269_, 2);
lean_inc_ref(v_body_321_);
lean_dec_ref_known(v_e_269_, 3);
v_d_277_ = v_binderType_320_;
v_b_278_ = v_body_321_;
v___y_279_ = v_a_270_;
v___y_280_ = v_a_271_;
v___y_281_ = v_a_272_;
v___y_282_ = v_a_273_;
v___y_283_ = v_a_274_;
goto v___jp_276_;
}
case 7:
{
lean_object* v_binderType_322_; lean_object* v_body_323_; 
v_binderType_322_ = lean_ctor_get(v_e_269_, 1);
lean_inc_ref(v_binderType_322_);
v_body_323_ = lean_ctor_get(v_e_269_, 2);
lean_inc_ref(v_body_323_);
lean_dec_ref_known(v_e_269_, 3);
v_d_277_ = v_binderType_322_;
v_b_278_ = v_body_323_;
v___y_279_ = v_a_270_;
v___y_280_ = v_a_271_;
v___y_281_ = v_a_272_;
v___y_282_ = v_a_273_;
v___y_283_ = v_a_274_;
goto v___jp_276_;
}
case 8:
{
lean_object* v_type_324_; lean_object* v_value_325_; lean_object* v_body_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_type_324_ = lean_ctor_get(v_e_269_, 1);
lean_inc_ref(v_type_324_);
v_value_325_ = lean_ctor_get(v_e_269_, 2);
lean_inc_ref(v_value_325_);
v_body_326_ = lean_ctor_get(v_e_269_, 3);
lean_inc_ref(v_body_326_);
lean_dec_ref_known(v_e_269_, 4);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_328_ = l_Lean_Core_checkSystem(v___x_327_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_type_324_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; uint8_t v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v___x_331_ = lean_unbox(v_a_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec_ref_known(v___x_329_, 1);
v___x_332_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_value_325_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; uint8_t v___x_334_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v___x_334_ = lean_unbox(v_a_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref_known(v___x_332_, 1);
v___x_335_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_body_326_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_335_;
}
else
{
lean_dec_ref(v_body_326_);
return v___x_332_;
}
}
else
{
lean_dec_ref(v_body_326_);
return v___x_332_;
}
}
else
{
lean_dec_ref(v_body_326_);
lean_dec_ref(v_value_325_);
return v___x_329_;
}
}
else
{
lean_dec_ref(v_body_326_);
lean_dec_ref(v_value_325_);
return v___x_329_;
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_body_326_);
lean_dec_ref(v_value_325_);
lean_dec_ref(v_type_324_);
v_a_336_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_328_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_328_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
case 10:
{
lean_object* v_expr_344_; lean_object* v___x_345_; 
v_expr_344_ = lean_ctor_get(v_e_269_, 1);
lean_inc_ref(v_expr_344_);
lean_dec_ref_known(v_e_269_, 2);
v___x_345_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_expr_344_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_345_;
}
case 11:
{
lean_object* v_struct_346_; lean_object* v___x_347_; 
v_struct_346_ = lean_ctor_get(v_e_269_, 2);
lean_inc_ref(v_struct_346_);
lean_dec_ref_known(v_e_269_, 3);
v___x_347_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_struct_346_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_347_;
}
default: 
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_e_269_);
v___x_348_ = 0;
v___x_349_ = lean_box(v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
v___jp_276_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0));
v___x_285_ = l_Lean_Core_checkSystem(v___x_284_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; 
lean_dec_ref_known(v___x_285_, 1);
v___x_286_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_d_277_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; uint8_t v___x_288_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v___x_288_ = lean_unbox(v_a_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_dec_ref_known(v___x_286_, 1);
v___x_289_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_b_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_289_;
}
else
{
lean_dec_ref(v_b_278_);
return v___x_286_;
}
}
else
{
lean_dec_ref(v_b_278_);
return v___x_286_;
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_b_278_);
lean_dec_ref(v_d_277_);
v_a_290_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_285_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_269_ = stack[0].m_obj;
lean_object* v_a_270_ = stack[1].m_obj;
lean_object* v_a_271_ = stack[2].m_obj;
lean_object* v_a_272_ = stack[3].m_obj;
lean_object* v_a_273_ = stack[4].m_obj;
lean_object* v_a_274_ = stack[5].m_obj;
lean_object* v_res_351_;
v_res_351_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_351_;
}
lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(lean_object* v_e_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_Expr_hasMVar(v_e_352_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_e_352_);
v___x_360_ = lean_box(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
else
{
uint8_t v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = 0;
v___x_363_ = lean_st_ref_get(v_a_353_);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v___x_363_, v_e_352_);
lean_dec(v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = lean_st_ref_take(v_a_353_);
v___x_366_ = lean_box(0);
lean_inc_ref(v_e_352_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_365_, v_e_352_, v___x_366_);
v___x_368_ = lean_st_ref_put(v_a_353_, v___x_367_);
v___x_369_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_e_352_);
v___x_370_ = lean_box(v___x_362_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_352_ = stack[0].m_obj;
lean_object* v_a_353_ = stack[1].m_obj;
lean_object* v_a_354_ = stack[2].m_obj;
lean_object* v_a_355_ = stack[3].m_obj;
lean_object* v_a_356_ = stack[4].m_obj;
lean_object* v_a_357_ = stack[5].m_obj;
lean_object* v_res_372_;
v_res_372_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_e_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(lean_object* v_e_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
return v_res_388_;
}
}
lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
return v___x_396_;
}
}
LEAN_EXPORT void l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_389_ = stack[0].m_obj;
lean_object* v___y_390_ = stack[1].m_obj;
lean_object* v___y_391_ = stack[2].m_obj;
lean_object* v___y_392_ = stack[3].m_obj;
lean_object* v___y_393_ = stack[4].m_obj;
lean_object* v___y_394_ = stack[5].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(lean_object* v_x_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
return v_res_405_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_407_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_407_ = stack[1].m_obj;
lean_object* v_a_408_ = stack[2].m_obj;
uint8_t v_res_410_;
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(lean_box(0), v_m_407_, v_a_408_);
stack->m_num = v_res_410_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(lean_object* v_00_u03b2_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(v_00_u03b2_411_, v_m_412_, v_a_413_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_m_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_417_, v_a_418_, v_b_419_);
return v___x_420_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_object* v_00_u03b2_421_, lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_422_, v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_422_ = stack[1].m_obj;
lean_object* v_x_423_ = stack[2].m_obj;
uint8_t v_res_425_;
v_res_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(lean_box(0), v_a_422_, v_x_423_);
stack->m_num = v_res_425_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(v_00_u03b2_426_, v_a_427_, v_x_428_);
lean_dec(v_x_428_);
lean_dec_ref(v_a_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(lean_object* v_00_u03b2_431_, lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_data_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_434_, lean_object* v_i_435_, lean_object* v_source_436_, lean_object* v_target_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v_i_435_, v_source_436_, v_target_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_440_, v_x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_unsigned_to_nat(16u);
v___x_445_ = lean_mk_array(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Meta_hasAssignableMVar___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__0, &l_Lean_Meta_hasAssignableMVar___closed__0_once, _init_l_Lean_Meta_hasAssignableMVar___closed__0);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
return v___x_448_;
}
}
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object* v_e_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Expr_hasMVar(v_e_449_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v_e_449_);
v___x_456_ = lean_box(v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Meta_hasAssignableMVar___closed__1, &l_Lean_Meta_hasAssignableMVar___closed__1_once, _init_l_Lean_Meta_hasAssignableMVar___closed__1);
v___x_459_ = lean_st_mk_ref(v___x_458_);
v___x_460_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(v_e_449_, v___x_459_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_st_ref_get(v___x_459_);
lean_dec(v___x_459_);
lean_dec(v___x_465_);
if (v_isShared_464_ == 0)
{
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_461_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_dec(v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_hasAssignableMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_449_ = stack[0].m_obj;
lean_object* v_a_450_ = stack[1].m_obj;
lean_object* v_a_451_ = stack[2].m_obj;
lean_object* v_a_452_ = stack[3].m_obj;
lean_object* v_a_453_ = stack[4].m_obj;
lean_object* v_res_470_;
v_res_470_ = l_Lean_Meta_hasAssignableMVar(v_e_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_hasAssignableMVar___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_hasAssignableMVar(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_477_;
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
