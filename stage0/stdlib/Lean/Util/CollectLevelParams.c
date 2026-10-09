// Lean compiler output
// Module: Lean.Util.CollectLevelParams
// Imports: public import Lean.Expr
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
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_level_eq(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__1;
static const lean_array_object l_Lean_CollectLevelParams_instInhabitedState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__2 = (const lean_object*)&l_Lean_CollectLevelParams_instInhabitedState___closed__2_value;
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__0, &l_Lean_CollectLevelParams_instInhabitedState___closed__0_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lean_CollectLevelParams_instInhabitedState___closed__2));
v___x_10_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__1, &l_Lean_CollectLevelParams_instInhabitedState___closed__1_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_ctor_set(v___x_11_, 2, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__3, &l_Lean_CollectLevelParams_instInhabitedState___closed__3_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__3);
return v___x_12_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
else
{
lean_object* v_key_16_; lean_object* v_tail_17_; uint8_t v___x_18_; 
v_key_16_ = lean_ctor_get(v_x_14_, 0);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v___x_18_ = lean_level_eq(v_key_16_, v_a_13_);
if (v___x_18_ == 0)
{
v_x_14_ = v_tail_17_;
goto _start;
}
else
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_13_ = stack[0].m_obj;
lean_object* v_x_14_ = stack[1].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_13_, v_x_14_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_a_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object* v_m_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_buckets_27_; lean_object* v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v_fold_32_; uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; size_t v___x_39_; size_t v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_buckets_27_ = lean_ctor_get(v_m_25_, 1);
v___x_28_ = lean_array_get_size(v_buckets_27_);
v___x_29_ = l_Lean_Level_hash(v_a_26_);
v___x_30_ = 32ULL;
v___x_31_ = lean_uint64_shift_right(v___x_29_, v___x_30_);
v_fold_32_ = lean_uint64_xor(v___x_29_, v___x_31_);
v___x_33_ = 16ULL;
v___x_34_ = lean_uint64_shift_right(v_fold_32_, v___x_33_);
v___x_35_ = lean_uint64_xor(v_fold_32_, v___x_34_);
v___x_36_ = lean_uint64_to_usize(v___x_35_);
v___x_37_ = lean_usize_of_nat(v___x_28_);
v___x_38_ = ((size_t)1ULL);
v___x_39_ = lean_usize_sub(v___x_37_, v___x_38_);
v___x_40_ = lean_usize_land(v___x_36_, v___x_39_);
v___x_41_ = lean_array_uget_borrowed(v_buckets_27_, v___x_40_);
v___x_42_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_26_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_25_ = stack[0].m_obj;
lean_object* v_a_26_ = stack[1].m_obj;
uint8_t v_res_43_;
v_res_43_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_25_, v_a_26_);
stack->m_num = v_res_43_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(lean_object* v_m_44_, lean_object* v_a_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_m_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
return v_x_48_;
}
else
{
lean_object* v_key_50_; lean_object* v_value_51_; lean_object* v_tail_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_75_; 
v_key_50_ = lean_ctor_get(v_x_49_, 0);
v_value_51_ = lean_ctor_get(v_x_49_, 1);
v_tail_52_ = lean_ctor_get(v_x_49_, 2);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_75_ == 0)
{
v___x_54_ = v_x_49_;
v_isShared_55_ = v_isSharedCheck_75_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_tail_52_);
lean_inc(v_value_51_);
lean_inc(v_key_50_);
lean_dec(v_x_49_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_75_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v_fold_60_; uint64_t v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_56_ = lean_array_get_size(v_x_48_);
v___x_57_ = l_Lean_Level_hash(v_key_50_);
v___x_58_ = 32ULL;
v___x_59_ = lean_uint64_shift_right(v___x_57_, v___x_58_);
v_fold_60_ = lean_uint64_xor(v___x_57_, v___x_59_);
v___x_61_ = 16ULL;
v___x_62_ = lean_uint64_shift_right(v_fold_60_, v___x_61_);
v___x_63_ = lean_uint64_xor(v_fold_60_, v___x_62_);
v___x_64_ = lean_uint64_to_usize(v___x_63_);
v___x_65_ = lean_usize_of_nat(v___x_56_);
v___x_66_ = ((size_t)1ULL);
v___x_67_ = lean_usize_sub(v___x_65_, v___x_66_);
v___x_68_ = lean_usize_land(v___x_64_, v___x_67_);
v___x_69_ = lean_array_uget_borrowed(v_x_48_, v___x_68_);
lean_inc(v___x_69_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 2, v___x_69_);
v___x_71_ = v___x_54_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_key_50_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_value_51_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___x_69_);
v___x_71_ = v_reuseFailAlloc_74_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_uset(v_x_48_, v___x_68_, v___x_71_);
v_x_48_ = v___x_72_;
v_x_49_ = v_tail_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object* v_i_76_, lean_object* v_source_77_, lean_object* v_target_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_array_get_size(v_source_77_);
v___x_80_ = lean_nat_dec_lt(v_i_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_source_77_);
lean_dec(v_i_76_);
return v_target_78_;
}
else
{
lean_object* v_es_81_; lean_object* v___x_82_; lean_object* v_source_83_; lean_object* v_target_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_es_81_ = lean_array_fget(v_source_77_, v_i_76_);
v___x_82_ = lean_box(0);
v_source_83_ = lean_array_fset(v_source_77_, v_i_76_, v___x_82_);
v_target_84_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_78_, v_es_81_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_76_, v___x_85_);
lean_dec(v_i_76_);
v_i_76_ = v___x_86_;
v_source_77_ = v_source_83_;
v_target_78_ = v_target_84_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(lean_object* v_data_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_nbuckets_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_89_ = lean_array_get_size(v_data_88_);
v___x_90_ = lean_unsigned_to_nat(2u);
v_nbuckets_91_ = lean_nat_mul(v___x_89_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v_nbuckets_91_, v___x_93_);
v___x_95_ = lean_array_propagate_mark(v_data_88_, v___x_94_);
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_92_, v_data_88_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_size_100_; lean_object* v_buckets_101_; lean_object* v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v_fold_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v_bkt_115_; uint8_t v___x_116_; 
v_size_100_ = lean_ctor_get(v_m_97_, 0);
v_buckets_101_ = lean_ctor_get(v_m_97_, 1);
v___x_102_ = lean_array_get_size(v_buckets_101_);
v___x_103_ = l_Lean_Level_hash(v_a_98_);
v___x_104_ = 32ULL;
v___x_105_ = lean_uint64_shift_right(v___x_103_, v___x_104_);
v_fold_106_ = lean_uint64_xor(v___x_103_, v___x_105_);
v___x_107_ = 16ULL;
v___x_108_ = lean_uint64_shift_right(v_fold_106_, v___x_107_);
v___x_109_ = lean_uint64_xor(v_fold_106_, v___x_108_);
v___x_110_ = lean_uint64_to_usize(v___x_109_);
v___x_111_ = lean_usize_of_nat(v___x_102_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_sub(v___x_111_, v___x_112_);
v___x_114_ = lean_usize_land(v___x_110_, v___x_113_);
v_bkt_115_ = lean_array_uget_borrowed(v_buckets_101_, v___x_114_);
v___x_116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_98_, v_bkt_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_137_; 
lean_inc_ref(v_buckets_101_);
lean_inc(v_size_100_);
v_isSharedCheck_137_ = !lean_is_exclusive(v_m_97_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; lean_object* v_unused_139_; 
v_unused_138_ = lean_ctor_get(v_m_97_, 1);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_m_97_, 0);
lean_dec(v_unused_139_);
v___x_118_ = v_m_97_;
v_isShared_119_ = v_isSharedCheck_137_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_m_97_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_137_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v_size_x27_121_; lean_object* v___x_122_; lean_object* v_buckets_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v_size_x27_121_ = lean_nat_add(v_size_100_, v___x_120_);
lean_dec(v_size_100_);
lean_inc(v_bkt_115_);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v_a_98_);
lean_ctor_set(v___x_122_, 1, v_b_99_);
lean_ctor_set(v___x_122_, 2, v_bkt_115_);
v_buckets_x27_123_ = lean_array_uset(v_buckets_101_, v___x_114_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(4u);
v___x_125_ = lean_nat_mul(v_size_x27_121_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(3u);
v___x_127_ = lean_nat_div(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_array_get_size(v_buckets_x27_123_);
v___x_129_ = lean_nat_dec_le(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v_val_130_; lean_object* v___x_132_; 
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_123_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_val_130_);
lean_ctor_set(v___x_118_, 0, v_size_x27_121_);
v___x_132_ = v___x_118_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_val_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_buckets_x27_123_);
lean_ctor_set(v___x_118_, 0, v_size_x27_121_);
v___x_135_ = v___x_118_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_buckets_x27_123_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_dec(v_b_99_);
lean_dec(v_a_98_);
return v_m_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object* v_x_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_u_143_; lean_object* v_v_144_; lean_object* v___y_145_; 
switch(lean_obj_tag(v_x_140_))
{
case 1:
{
lean_object* v_a_148_; lean_object* v___x_149_; 
v_a_148_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v_x_140_, 1);
v___x_149_ = l_Lean_CollectLevelParams_visitLevel(v_a_148_, v_a_141_);
return v___x_149_;
}
case 2:
{
lean_object* v_a_150_; lean_object* v_a_151_; 
v_a_150_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_150_);
v_a_151_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_a_151_);
lean_dec_ref_known(v_x_140_, 2);
v_u_143_ = v_a_150_;
v_v_144_ = v_a_151_;
v___y_145_ = v_a_141_;
goto v___jp_142_;
}
case 3:
{
lean_object* v_a_152_; lean_object* v_a_153_; 
v_a_152_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_152_);
v_a_153_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_a_153_);
lean_dec_ref_known(v_x_140_, 2);
v_u_143_ = v_a_152_;
v_v_144_ = v_a_153_;
v___y_145_ = v_a_141_;
goto v___jp_142_;
}
case 4:
{
lean_object* v_a_154_; lean_object* v_visitedLevel_155_; lean_object* v_visitedExpr_156_; lean_object* v_params_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_a_154_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v_x_140_, 1);
v_visitedLevel_155_ = lean_ctor_get(v_a_141_, 0);
v_visitedExpr_156_ = lean_ctor_get(v_a_141_, 1);
v_params_157_ = lean_ctor_get(v_a_141_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v_a_141_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_params_157_);
lean_inc(v_visitedExpr_156_);
lean_inc(v_visitedLevel_155_);
lean_dec(v_a_141_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_array_push(v_params_157_, v_a_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 2, v___x_161_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_visitedLevel_155_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_visitedExpr_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
default: 
{
lean_dec(v_x_140_);
return v_a_141_;
}
}
v___jp_142_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = l_Lean_CollectLevelParams_visitLevel(v_u_143_, v___y_145_);
v___x_147_ = l_Lean_CollectLevelParams_visitLevel(v_v_144_, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* v_u_166_, lean_object* v_s_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Level_hasParam(v_u_166_);
if (v___x_168_ == 0)
{
lean_dec(v_u_166_);
return v_s_167_;
}
else
{
lean_object* v_visitedLevel_169_; lean_object* v_visitedExpr_170_; lean_object* v_params_171_; uint8_t v___x_172_; 
v_visitedLevel_169_ = lean_ctor_get(v_s_167_, 0);
v_visitedExpr_170_ = lean_ctor_get(v_s_167_, 1);
v_params_171_ = lean_ctor_get(v_s_167_, 2);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_169_, v_u_166_);
if (v___x_172_ == 0)
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_params_171_);
lean_inc_ref(v_visitedExpr_170_);
lean_inc_ref(v_visitedLevel_169_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_s_167_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_183_ = lean_ctor_get(v_s_167_, 2);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_s_167_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_s_167_, 0);
lean_dec(v_unused_185_);
v___x_174_ = v_s_167_;
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
else
{
lean_dec(v_s_167_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_box(0);
lean_inc(v_u_166_);
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_169_, v_u_166_, v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_visitedExpr_170_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_params_171_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_CollectLevelParams_collect(v_u_166_, v___x_179_);
return v___x_180_;
}
}
}
else
{
lean_dec(v_u_166_);
return v_s_167_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_187_, v_a_188_);
return v___x_189_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
uint8_t v_res_190_;
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_box(0), v_m_187_, v_a_188_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_191_, lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(v_00_u03b2_191_, v_m_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_m_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object* v_00_u03b2_196_, lean_object* v_m_197_, lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_197_, v_a_198_, v_b_199_);
return v___x_200_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[1].m_obj;
lean_object* v_x_203_ = stack[2].m_obj;
uint8_t v_res_205_;
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_box(0), v_a_202_, v_x_203_);
stack->m_num = v_res_205_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_206_, lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(v_00_u03b2_206_, v_a_207_, v_x_208_);
lean_dec(v_x_208_);
lean_dec(v_a_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_211_, lean_object* v_data_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_data_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_214_, lean_object* v_i_215_, lean_object* v_source_216_, lean_object* v_target_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_215_, v_source_216_, v_target_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
return v_x_223_;
}
else
{
lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_227_; 
v_head_225_ = lean_ctor_get(v_x_224_, 0);
lean_inc(v_head_225_);
v_tail_226_ = lean_ctor_get(v_x_224_, 1);
lean_inc(v_tail_226_);
lean_dec_ref_known(v_x_224_, 2);
v___x_227_ = l_Lean_CollectLevelParams_visitLevel(v_head_225_, v_x_223_);
v_x_223_ = v___x_227_;
v_x_224_ = v_tail_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object* v_us_229_, lean_object* v_s_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_s_230_, v_us_229_);
return v___x_231_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
else
{
lean_object* v_key_235_; lean_object* v_tail_236_; uint8_t v___x_237_; 
v_key_235_ = lean_ctor_get(v_x_233_, 0);
v_tail_236_ = lean_ctor_get(v_x_233_, 2);
v___x_237_ = lean_expr_eqv(v_key_235_, v_a_232_);
if (v___x_237_ == 0)
{
v_x_233_ = v_tail_236_;
goto _start;
}
else
{
return v___x_237_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_232_ = stack[0].m_obj;
lean_object* v_x_233_ = stack[1].m_obj;
uint8_t v_res_239_;
v_res_239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_232_, v_x_233_);
stack->m_num = v_res_239_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object* v_a_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_240_, v_x_241_);
lean_dec(v_x_241_);
lean_dec_ref(v_a_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object* v_m_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_buckets_246_; lean_object* v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v_fold_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_buckets_246_ = lean_ctor_get(v_m_244_, 1);
v___x_247_ = lean_array_get_size(v_buckets_246_);
v___x_248_ = l_Lean_Expr_hash(v_a_245_);
v___x_249_ = 32ULL;
v___x_250_ = lean_uint64_shift_right(v___x_248_, v___x_249_);
v_fold_251_ = lean_uint64_xor(v___x_248_, v___x_250_);
v___x_252_ = 16ULL;
v___x_253_ = lean_uint64_shift_right(v_fold_251_, v___x_252_);
v___x_254_ = lean_uint64_xor(v_fold_251_, v___x_253_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = lean_usize_of_nat(v___x_247_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_sub(v___x_256_, v___x_257_);
v___x_259_ = lean_usize_land(v___x_255_, v___x_258_);
v___x_260_ = lean_array_uget_borrowed(v_buckets_246_, v___x_259_);
v___x_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_245_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_244_ = stack[0].m_obj;
lean_object* v_a_245_ = stack[1].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_244_, v_a_245_);
stack->m_num = v_res_262_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_263_, v_a_264_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_m_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
return v_x_267_;
}
else
{
lean_object* v_key_269_; lean_object* v_value_270_; lean_object* v_tail_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v_key_269_ = lean_ctor_get(v_x_268_, 0);
v_value_270_ = lean_ctor_get(v_x_268_, 1);
v_tail_271_ = lean_ctor_get(v_x_268_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v_x_268_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tail_271_);
lean_inc(v_value_270_);
lean_inc(v_key_269_);
lean_dec(v_x_268_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v_fold_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_275_ = lean_array_get_size(v_x_267_);
v___x_276_ = l_Lean_Expr_hash(v_key_269_);
v___x_277_ = 32ULL;
v___x_278_ = lean_uint64_shift_right(v___x_276_, v___x_277_);
v_fold_279_ = lean_uint64_xor(v___x_276_, v___x_278_);
v___x_280_ = 16ULL;
v___x_281_ = lean_uint64_shift_right(v_fold_279_, v___x_280_);
v___x_282_ = lean_uint64_xor(v_fold_279_, v___x_281_);
v___x_283_ = lean_uint64_to_usize(v___x_282_);
v___x_284_ = lean_usize_of_nat(v___x_275_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_sub(v___x_284_, v___x_285_);
v___x_287_ = lean_usize_land(v___x_283_, v___x_286_);
v___x_288_ = lean_array_uget_borrowed(v_x_267_, v___x_287_);
lean_inc(v___x_288_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 2, v___x_288_);
v___x_290_ = v___x_273_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_key_269_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_value_270_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v___x_288_);
v___x_290_ = v_reuseFailAlloc_293_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_array_uset(v_x_267_, v___x_287_, v___x_290_);
v_x_267_ = v___x_291_;
v_x_268_ = v_tail_271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(lean_object* v_i_295_, lean_object* v_source_296_, lean_object* v_target_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_source_296_);
v___x_299_ = lean_nat_dec_lt(v_i_295_, v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_source_296_);
lean_dec(v_i_295_);
return v_target_297_;
}
else
{
lean_object* v_es_300_; lean_object* v___x_301_; lean_object* v_source_302_; lean_object* v_target_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_es_300_ = lean_array_fget(v_source_296_, v_i_295_);
v___x_301_ = lean_box(0);
v_source_302_ = lean_array_fset(v_source_296_, v_i_295_, v___x_301_);
v_target_303_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_target_297_, v_es_300_);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_i_295_, v___x_304_);
lean_dec(v_i_295_);
v_i_295_ = v___x_305_;
v_source_296_ = v_source_302_;
v_target_297_ = v_target_303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object* v_data_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_nbuckets_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_308_ = lean_array_get_size(v_data_307_);
v___x_309_ = lean_unsigned_to_nat(2u);
v_nbuckets_310_ = lean_nat_mul(v___x_308_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_box(0);
v___x_313_ = lean_mk_array(v_nbuckets_310_, v___x_312_);
v___x_314_ = lean_array_propagate_mark(v_data_307_, v___x_313_);
v___x_315_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v___x_311_, v_data_307_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object* v_m_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v_size_319_; lean_object* v_buckets_320_; lean_object* v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_bkt_334_; uint8_t v___x_335_; 
v_size_319_ = lean_ctor_get(v_m_316_, 0);
v_buckets_320_ = lean_ctor_get(v_m_316_, 1);
v___x_321_ = lean_array_get_size(v_buckets_320_);
v___x_322_ = l_Lean_Expr_hash(v_a_317_);
v___x_323_ = 32ULL;
v___x_324_ = lean_uint64_shift_right(v___x_322_, v___x_323_);
v_fold_325_ = lean_uint64_xor(v___x_322_, v___x_324_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_321_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v_bkt_334_ = lean_array_uget_borrowed(v_buckets_320_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_317_, v_bkt_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_356_; 
lean_inc_ref(v_buckets_320_);
lean_inc(v_size_319_);
v_isSharedCheck_356_ = !lean_is_exclusive(v_m_316_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_357_ = lean_ctor_get(v_m_316_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_m_316_, 0);
lean_dec(v_unused_358_);
v___x_337_ = v_m_316_;
v_isShared_338_ = v_isSharedCheck_356_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_m_316_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_356_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v_size_x27_340_; lean_object* v___x_341_; lean_object* v_buckets_x27_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v_size_x27_340_ = lean_nat_add(v_size_319_, v___x_339_);
lean_dec(v_size_319_);
lean_inc(v_bkt_334_);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v_a_317_);
lean_ctor_set(v___x_341_, 1, v_b_318_);
lean_ctor_set(v___x_341_, 2, v_bkt_334_);
v_buckets_x27_342_ = lean_array_uset(v_buckets_320_, v___x_333_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = lean_nat_mul(v_size_x27_340_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(3u);
v___x_346_ = lean_nat_div(v___x_344_, v___x_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_array_get_size(v_buckets_x27_342_);
v___x_348_ = lean_nat_dec_le(v___x_346_, v___x_347_);
lean_dec(v___x_346_);
if (v___x_348_ == 0)
{
lean_object* v_val_349_; lean_object* v___x_351_; 
v_val_349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_buckets_x27_342_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_val_349_);
lean_ctor_set(v___x_337_, 0, v_size_x27_340_);
v___x_351_ = v___x_337_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_x27_340_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_val_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
lean_object* v___x_354_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_buckets_x27_342_);
lean_ctor_set(v___x_337_, 0, v_size_x27_340_);
v___x_354_ = v___x_337_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_size_x27_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_buckets_x27_342_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_dec(v_b_318_);
lean_dec_ref(v_a_317_);
return v_m_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object* v_x_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_d_362_; lean_object* v_b_363_; lean_object* v___y_364_; 
switch(lean_obj_tag(v_x_359_))
{
case 11:
{
lean_object* v_struct_367_; lean_object* v___x_368_; 
v_struct_367_ = lean_ctor_get(v_x_359_, 2);
lean_inc_ref(v_struct_367_);
lean_dec_ref_known(v_x_359_, 3);
v___x_368_ = l_Lean_CollectLevelParams_visitExpr(v_struct_367_, v_a_360_);
return v___x_368_;
}
case 7:
{
lean_object* v_binderType_369_; lean_object* v_body_370_; 
v_binderType_369_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_binderType_369_);
v_body_370_ = lean_ctor_get(v_x_359_, 2);
lean_inc_ref(v_body_370_);
lean_dec_ref_known(v_x_359_, 3);
v_d_362_ = v_binderType_369_;
v_b_363_ = v_body_370_;
v___y_364_ = v_a_360_;
goto v___jp_361_;
}
case 6:
{
lean_object* v_binderType_371_; lean_object* v_body_372_; 
v_binderType_371_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_binderType_371_);
v_body_372_ = lean_ctor_get(v_x_359_, 2);
lean_inc_ref(v_body_372_);
lean_dec_ref_known(v_x_359_, 3);
v_d_362_ = v_binderType_371_;
v_b_363_ = v_body_372_;
v___y_364_ = v_a_360_;
goto v___jp_361_;
}
case 8:
{
lean_object* v_type_373_; lean_object* v_value_374_; lean_object* v_body_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_type_373_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_type_373_);
v_value_374_ = lean_ctor_get(v_x_359_, 2);
lean_inc_ref(v_value_374_);
v_body_375_ = lean_ctor_get(v_x_359_, 3);
lean_inc_ref(v_body_375_);
lean_dec_ref_known(v_x_359_, 4);
v___x_376_ = l_Lean_CollectLevelParams_visitExpr(v_type_373_, v_a_360_);
v___x_377_ = l_Lean_CollectLevelParams_visitExpr(v_value_374_, v___x_376_);
v___x_378_ = l_Lean_CollectLevelParams_visitExpr(v_body_375_, v___x_377_);
return v___x_378_;
}
case 5:
{
lean_object* v_fn_379_; lean_object* v_arg_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_fn_379_ = lean_ctor_get(v_x_359_, 0);
lean_inc_ref(v_fn_379_);
v_arg_380_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_arg_380_);
lean_dec_ref_known(v_x_359_, 2);
v___x_381_ = l_Lean_CollectLevelParams_visitExpr(v_fn_379_, v_a_360_);
v___x_382_ = l_Lean_CollectLevelParams_visitExpr(v_arg_380_, v___x_381_);
return v___x_382_;
}
case 10:
{
lean_object* v_expr_383_; lean_object* v___x_384_; 
v_expr_383_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_expr_383_);
lean_dec_ref_known(v_x_359_, 2);
v___x_384_ = l_Lean_CollectLevelParams_visitExpr(v_expr_383_, v_a_360_);
return v___x_384_;
}
case 4:
{
lean_object* v_us_385_; lean_object* v___x_386_; 
v_us_385_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_us_385_);
lean_dec_ref_known(v_x_359_, 2);
v___x_386_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_a_360_, v_us_385_);
return v___x_386_;
}
case 3:
{
lean_object* v_u_387_; lean_object* v___x_388_; 
v_u_387_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_u_387_);
lean_dec_ref_known(v_x_359_, 1);
v___x_388_ = l_Lean_CollectLevelParams_visitLevel(v_u_387_, v_a_360_);
return v___x_388_;
}
default: 
{
lean_dec_ref(v_x_359_);
return v_a_360_;
}
}
v___jp_361_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = l_Lean_CollectLevelParams_visitExpr(v_d_362_, v___y_364_);
v___x_366_ = l_Lean_CollectLevelParams_visitExpr(v_b_363_, v___x_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object* v_e_389_, lean_object* v_s_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_Expr_hasLevelParam(v_e_389_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_e_389_);
return v_s_390_;
}
else
{
lean_object* v_visitedLevel_392_; lean_object* v_visitedExpr_393_; lean_object* v_params_394_; uint8_t v___x_395_; 
v_visitedLevel_392_ = lean_ctor_get(v_s_390_, 0);
v_visitedExpr_393_ = lean_ctor_get(v_s_390_, 1);
v_params_394_ = lean_ctor_get(v_s_390_, 2);
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_visitedExpr_393_, v_e_389_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
lean_inc_ref(v_params_394_);
lean_inc_ref(v_visitedExpr_393_);
lean_inc_ref(v_visitedLevel_392_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_s_390_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_406_ = lean_ctor_get(v_s_390_, 2);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_s_390_, 1);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_s_390_, 0);
lean_dec(v_unused_408_);
v___x_397_ = v_s_390_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_s_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
lean_inc_ref(v_e_389_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_visitedExpr_393_, v_e_389_, v___x_399_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_visitedLevel_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_params_394_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_CollectLevelParams_main(v_e_389_, v___x_402_);
return v___x_403_;
}
}
}
else
{
lean_dec_ref(v_e_389_);
return v_s_390_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_410_, v_a_411_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_410_ = stack[1].m_obj;
lean_object* v_a_411_ = stack[2].m_obj;
uint8_t v_res_413_;
v_res_413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_box(0), v_m_410_, v_a_411_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_414_, lean_object* v_m_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(v_00_u03b2_414_, v_m_415_, v_a_416_);
lean_dec_ref(v_a_416_);
lean_dec_ref(v_m_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object* v_00_u03b2_419_, lean_object* v_m_420_, lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_420_, v_a_421_, v_b_422_);
return v___x_423_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_425_ = stack[1].m_obj;
lean_object* v_x_426_ = stack[2].m_obj;
uint8_t v_res_428_;
v_res_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_box(0), v_a_425_, v_x_426_);
stack->m_num = v_res_428_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(v_00_u03b2_429_, v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_a_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object* v_00_u03b2_434_, lean_object* v_data_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_data_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_437_, lean_object* v_i_438_, lean_object* v_source_439_, lean_object* v_target_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v_i_438_, v_source_439_, v_target_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object* v_s_446_, lean_object* v_pre_447_, lean_object* v_i_448_){
_start:
{
lean_object* v_visitedLevel_449_; lean_object* v___x_450_; lean_object* v_v_451_; uint8_t v___x_452_; 
v_visitedLevel_449_ = lean_ctor_get(v_s_446_, 0);
lean_inc(v_i_448_);
lean_inc(v_pre_447_);
v___x_450_ = lean_name_append_index_after(v_pre_447_, v_i_448_);
v_v_451_ = l_Lean_mkLevelParam(v___x_450_);
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_449_, v_v_451_);
if (v___x_452_ == 0)
{
lean_dec(v_i_448_);
lean_dec(v_pre_447_);
return v_v_451_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_v_451_);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_i_448_, v___x_453_);
lean_dec(v_i_448_);
v_i_448_ = v___x_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object* v_s_456_, lean_object* v_pre_457_, lean_object* v_i_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_456_, v_pre_457_, v_i_458_);
lean_dec_ref(v_s_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object* v_s_460_, lean_object* v_pre_461_){
_start:
{
lean_object* v_visitedLevel_462_; lean_object* v_v_463_; uint8_t v___x_464_; 
v_visitedLevel_462_ = lean_ctor_get(v_s_460_, 0);
lean_inc(v_pre_461_);
v_v_463_ = l_Lean_mkLevelParam(v_pre_461_);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_462_, v_v_463_);
if (v___x_464_ == 0)
{
lean_dec(v_pre_461_);
return v_v_463_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_v_463_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_460_, v_pre_461_, v___x_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object* v_s_467_, lean_object* v_pre_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_CollectLevelParams_State_getUnusedLevelParam(v_s_467_, v_pre_468_);
lean_dec_ref(v_s_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object* v_s_470_, lean_object* v_e_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_CollectLevelParams_main(v_e_471_, v_s_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object* v_s_473_, lean_object* v_e_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_CollectLevelParams_main(v_e_474_, v_s_473_);
return v___x_475_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelParams_instInhabitedState = _init_l_Lean_CollectLevelParams_instInhabitedState();
lean_mark_persistent(l_Lean_CollectLevelParams_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLevelParams(builtin);
}
#ifdef __cplusplus
}
#endif
