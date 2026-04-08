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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v_a_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object* v_m_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_buckets_26_; lean_object* v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v_fold_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_buckets_26_ = lean_ctor_get(v_m_24_, 1);
v___x_27_ = lean_array_get_size(v_buckets_26_);
v___x_28_ = l_Lean_Level_hash(v_a_25_);
v___x_29_ = 32ULL;
v___x_30_ = lean_uint64_shift_right(v___x_28_, v___x_29_);
v_fold_31_ = lean_uint64_xor(v___x_28_, v___x_30_);
v___x_32_ = 16ULL;
v___x_33_ = lean_uint64_shift_right(v_fold_31_, v___x_32_);
v___x_34_ = lean_uint64_xor(v_fold_31_, v___x_33_);
v___x_35_ = lean_uint64_to_usize(v___x_34_);
v___x_36_ = lean_usize_of_nat(v___x_27_);
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_sub(v___x_36_, v___x_37_);
v___x_39_ = lean_usize_land(v___x_35_, v___x_38_);
v___x_40_ = lean_array_uget_borrowed(v_buckets_26_, v___x_39_);
v___x_41_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_25_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(lean_object* v_m_42_, lean_object* v_a_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_42_, v_a_43_);
lean_dec(v_a_43_);
lean_dec_ref(v_m_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
return v_x_46_;
}
else
{
lean_object* v_key_48_; lean_object* v_value_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_73_; 
v_key_48_ = lean_ctor_get(v_x_47_, 0);
v_value_49_ = lean_ctor_get(v_x_47_, 1);
v_tail_50_ = lean_ctor_get(v_x_47_, 2);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_73_ == 0)
{
v___x_52_ = v_x_47_;
v_isShared_53_ = v_isSharedCheck_73_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_value_49_);
lean_inc(v_key_48_);
lean_dec(v_x_47_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_73_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v_fold_58_; uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_54_ = lean_array_get_size(v_x_46_);
v___x_55_ = l_Lean_Level_hash(v_key_48_);
v___x_56_ = 32ULL;
v___x_57_ = lean_uint64_shift_right(v___x_55_, v___x_56_);
v_fold_58_ = lean_uint64_xor(v___x_55_, v___x_57_);
v___x_59_ = 16ULL;
v___x_60_ = lean_uint64_shift_right(v_fold_58_, v___x_59_);
v___x_61_ = lean_uint64_xor(v_fold_58_, v___x_60_);
v___x_62_ = lean_uint64_to_usize(v___x_61_);
v___x_63_ = lean_usize_of_nat(v___x_54_);
v___x_64_ = ((size_t)1ULL);
v___x_65_ = lean_usize_sub(v___x_63_, v___x_64_);
v___x_66_ = lean_usize_land(v___x_62_, v___x_65_);
v___x_67_ = lean_array_uget_borrowed(v_x_46_, v___x_66_);
lean_inc(v___x_67_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 2, v___x_67_);
v___x_69_ = v___x_52_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_key_48_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_value_49_);
lean_ctor_set(v_reuseFailAlloc_72_, 2, v___x_67_);
v___x_69_ = v_reuseFailAlloc_72_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; 
v___x_70_ = lean_array_uset(v_x_46_, v___x_66_, v___x_69_);
v_x_46_ = v___x_70_;
v_x_47_ = v_tail_50_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object* v_i_74_, lean_object* v_source_75_, lean_object* v_target_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_array_get_size(v_source_75_);
v___x_78_ = lean_nat_dec_lt(v_i_74_, v___x_77_);
if (v___x_78_ == 0)
{
lean_dec_ref(v_source_75_);
lean_dec(v_i_74_);
return v_target_76_;
}
else
{
lean_object* v_es_79_; lean_object* v___x_80_; lean_object* v_source_81_; lean_object* v_target_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_es_79_ = lean_array_fget(v_source_75_, v_i_74_);
v___x_80_ = lean_box(0);
v_source_81_ = lean_array_fset(v_source_75_, v_i_74_, v___x_80_);
v_target_82_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_76_, v_es_79_);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_add(v_i_74_, v___x_83_);
lean_dec(v_i_74_);
v_i_74_ = v___x_84_;
v_source_75_ = v_source_81_;
v_target_76_ = v_target_82_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(lean_object* v_data_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_nbuckets_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_87_ = lean_array_get_size(v_data_86_);
v___x_88_ = lean_unsigned_to_nat(2u);
v_nbuckets_89_ = lean_nat_mul(v___x_87_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_box(0);
v___x_92_ = lean_mk_array(v_nbuckets_89_, v___x_91_);
v___x_93_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_90_, v_data_86_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object* v_m_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_size_97_; lean_object* v_buckets_98_; lean_object* v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v_fold_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_bkt_112_; uint8_t v___x_113_; 
v_size_97_ = lean_ctor_get(v_m_94_, 0);
v_buckets_98_ = lean_ctor_get(v_m_94_, 1);
v___x_99_ = lean_array_get_size(v_buckets_98_);
v___x_100_ = l_Lean_Level_hash(v_a_95_);
v___x_101_ = 32ULL;
v___x_102_ = lean_uint64_shift_right(v___x_100_, v___x_101_);
v_fold_103_ = lean_uint64_xor(v___x_100_, v___x_102_);
v___x_104_ = 16ULL;
v___x_105_ = lean_uint64_shift_right(v_fold_103_, v___x_104_);
v___x_106_ = lean_uint64_xor(v_fold_103_, v___x_105_);
v___x_107_ = lean_uint64_to_usize(v___x_106_);
v___x_108_ = lean_usize_of_nat(v___x_99_);
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_land(v___x_107_, v___x_110_);
v_bkt_112_ = lean_array_uget_borrowed(v_buckets_98_, v___x_111_);
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_95_, v_bkt_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_buckets_98_);
lean_inc(v_size_97_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_m_94_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_m_94_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_m_94_, 0);
lean_dec(v_unused_136_);
v___x_115_ = v_m_94_;
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
else
{
lean_dec(v_m_94_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v_size_x27_118_; lean_object* v___x_119_; lean_object* v_buckets_x27_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v_size_x27_118_ = lean_nat_add(v_size_97_, v___x_117_);
lean_dec(v_size_97_);
lean_inc(v_bkt_112_);
v___x_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_119_, 0, v_a_95_);
lean_ctor_set(v___x_119_, 1, v_b_96_);
lean_ctor_set(v___x_119_, 2, v_bkt_112_);
v_buckets_x27_120_ = lean_array_uset(v_buckets_98_, v___x_111_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_mul(v_size_x27_118_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(3u);
v___x_124_ = lean_nat_div(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_array_get_size(v_buckets_x27_120_);
v___x_126_ = lean_nat_dec_le(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v_val_127_; lean_object* v___x_129_; 
v_val_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_120_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_val_127_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_129_ = v___x_115_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_val_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_132_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_buckets_x27_120_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_132_ = v___x_115_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_buckets_x27_120_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_dec(v_b_96_);
lean_dec(v_a_95_);
return v_m_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object* v_x_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_u_140_; lean_object* v_v_141_; lean_object* v___y_142_; 
switch(lean_obj_tag(v_x_137_))
{
case 1:
{
lean_object* v_a_145_; lean_object* v___x_146_; 
v_a_145_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v_x_137_);
v___x_146_ = l_Lean_CollectLevelParams_visitLevel(v_a_145_, v_a_138_);
return v___x_146_;
}
case 2:
{
lean_object* v_a_147_; lean_object* v_a_148_; 
v_a_147_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_147_);
v_a_148_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_a_148_);
lean_dec_ref(v_x_137_);
v_u_140_ = v_a_147_;
v_v_141_ = v_a_148_;
v___y_142_ = v_a_138_;
goto v___jp_139_;
}
case 3:
{
lean_object* v_a_149_; lean_object* v_a_150_; 
v_a_149_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_149_);
v_a_150_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_a_150_);
lean_dec_ref(v_x_137_);
v_u_140_ = v_a_149_;
v_v_141_ = v_a_150_;
v___y_142_ = v_a_138_;
goto v___jp_139_;
}
case 4:
{
lean_object* v_a_151_; lean_object* v_visitedLevel_152_; lean_object* v_visitedExpr_153_; lean_object* v_params_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_a_151_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v_x_137_);
v_visitedLevel_152_ = lean_ctor_get(v_a_138_, 0);
v_visitedExpr_153_ = lean_ctor_get(v_a_138_, 1);
v_params_154_ = lean_ctor_get(v_a_138_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_138_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_a_138_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_params_154_);
lean_inc(v_visitedExpr_153_);
lean_inc(v_visitedLevel_152_);
lean_dec(v_a_138_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_array_push(v_params_154_, v_a_151_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 2, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_visitedLevel_152_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_visitedExpr_153_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
default: 
{
lean_dec(v_x_137_);
return v_a_138_;
}
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Lean_CollectLevelParams_visitLevel(v_u_140_, v___y_142_);
v___x_144_ = l_Lean_CollectLevelParams_visitLevel(v_v_141_, v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* v_u_163_, lean_object* v_s_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Level_hasParam(v_u_163_);
if (v___x_165_ == 0)
{
lean_dec(v_u_163_);
return v_s_164_;
}
else
{
lean_object* v_visitedLevel_166_; lean_object* v_visitedExpr_167_; lean_object* v_params_168_; uint8_t v___x_169_; 
v_visitedLevel_166_ = lean_ctor_get(v_s_164_, 0);
v_visitedExpr_167_ = lean_ctor_get(v_s_164_, 1);
v_params_168_ = lean_ctor_get(v_s_164_, 2);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_166_, v_u_163_);
if (v___x_169_ == 0)
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
lean_inc_ref(v_params_168_);
lean_inc_ref(v_visitedExpr_167_);
lean_inc_ref(v_visitedLevel_166_);
v_isSharedCheck_179_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; 
v_unused_180_ = lean_ctor_get(v_s_164_, 2);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_s_164_, 1);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_s_164_, 0);
lean_dec(v_unused_182_);
v___x_171_ = v_s_164_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_s_164_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_box(0);
lean_inc(v_u_163_);
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_166_, v_u_163_, v___x_173_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_174_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_visitedExpr_167_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_params_168_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_CollectLevelParams_collect(v_u_163_, v___x_176_);
return v___x_177_;
}
}
}
else
{
lean_dec(v_u_163_);
return v_s_164_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object* v_00_u03b2_183_, lean_object* v_m_184_, lean_object* v_a_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_184_, v_a_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(v_00_u03b2_187_, v_m_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_m_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object* v_00_u03b2_192_, lean_object* v_m_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_193_, v_a_194_, v_b_195_);
return v___x_196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_197_, lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_198_, v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(v_00_u03b2_201_, v_a_202_, v_x_203_);
lean_dec(v_x_203_);
lean_dec(v_a_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_206_, lean_object* v_data_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_data_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_209_, lean_object* v_i_210_, lean_object* v_source_211_, lean_object* v_target_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_210_, v_source_211_, v_target_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
return v_x_218_;
}
else
{
lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v___x_222_; 
v_head_220_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_head_220_);
v_tail_221_ = lean_ctor_get(v_x_219_, 1);
lean_inc(v_tail_221_);
lean_dec_ref(v_x_219_);
v___x_222_ = l_Lean_CollectLevelParams_visitLevel(v_head_220_, v_x_218_);
v_x_218_ = v___x_222_;
v_x_219_ = v_tail_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object* v_us_224_, lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_s_225_, v_us_224_);
return v___x_226_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
else
{
lean_object* v_key_230_; lean_object* v_tail_231_; uint8_t v___x_232_; 
v_key_230_ = lean_ctor_get(v_x_228_, 0);
v_tail_231_ = lean_ctor_get(v_x_228_, 2);
v___x_232_ = lean_expr_eqv(v_key_230_, v_a_227_);
if (v___x_232_ == 0)
{
v_x_228_ = v_tail_231_;
goto _start;
}
else
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object* v_a_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_234_, v_x_235_);
lean_dec(v_x_235_);
lean_dec_ref(v_a_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_buckets_240_; lean_object* v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v_fold_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_buckets_240_ = lean_ctor_get(v_m_238_, 1);
v___x_241_ = lean_array_get_size(v_buckets_240_);
v___x_242_ = l_Lean_Expr_hash(v_a_239_);
v___x_243_ = 32ULL;
v___x_244_ = lean_uint64_shift_right(v___x_242_, v___x_243_);
v_fold_245_ = lean_uint64_xor(v___x_242_, v___x_244_);
v___x_246_ = 16ULL;
v___x_247_ = lean_uint64_shift_right(v_fold_245_, v___x_246_);
v___x_248_ = lean_uint64_xor(v_fold_245_, v___x_247_);
v___x_249_ = lean_uint64_to_usize(v___x_248_);
v___x_250_ = lean_usize_of_nat(v___x_241_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_sub(v___x_250_, v___x_251_);
v___x_253_ = lean_usize_land(v___x_249_, v___x_252_);
v___x_254_ = lean_array_uget_borrowed(v_buckets_240_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_239_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object* v_m_256_, lean_object* v_a_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_256_, v_a_257_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_m_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
return v_x_260_;
}
else
{
lean_object* v_key_262_; lean_object* v_value_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_287_; 
v_key_262_ = lean_ctor_get(v_x_261_, 0);
v_value_263_ = lean_ctor_get(v_x_261_, 1);
v_tail_264_ = lean_ctor_get(v_x_261_, 2);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_287_ == 0)
{
v___x_266_ = v_x_261_;
v_isShared_267_ = v_isSharedCheck_287_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_value_263_);
lean_inc(v_key_262_);
lean_dec(v_x_261_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_287_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v_fold_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_268_ = lean_array_get_size(v_x_260_);
v___x_269_ = l_Lean_Expr_hash(v_key_262_);
v___x_270_ = 32ULL;
v___x_271_ = lean_uint64_shift_right(v___x_269_, v___x_270_);
v_fold_272_ = lean_uint64_xor(v___x_269_, v___x_271_);
v___x_273_ = 16ULL;
v___x_274_ = lean_uint64_shift_right(v_fold_272_, v___x_273_);
v___x_275_ = lean_uint64_xor(v_fold_272_, v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = lean_usize_of_nat(v___x_268_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v___x_277_, v___x_278_);
v___x_280_ = lean_usize_land(v___x_276_, v___x_279_);
v___x_281_ = lean_array_uget_borrowed(v_x_260_, v___x_280_);
lean_inc(v___x_281_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v___x_281_);
v___x_283_ = v___x_266_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_key_262_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_value_263_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v___x_281_);
v___x_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_uset(v_x_260_, v___x_280_, v___x_283_);
v_x_260_ = v___x_284_;
v_x_261_ = v_tail_264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(lean_object* v_i_288_, lean_object* v_source_289_, lean_object* v_target_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_source_289_);
v___x_292_ = lean_nat_dec_lt(v_i_288_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec_ref(v_source_289_);
lean_dec(v_i_288_);
return v_target_290_;
}
else
{
lean_object* v_es_293_; lean_object* v___x_294_; lean_object* v_source_295_; lean_object* v_target_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_es_293_ = lean_array_fget(v_source_289_, v_i_288_);
v___x_294_ = lean_box(0);
v_source_295_ = lean_array_fset(v_source_289_, v_i_288_, v___x_294_);
v_target_296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_target_290_, v_es_293_);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_288_, v___x_297_);
lean_dec(v_i_288_);
v_i_288_ = v___x_298_;
v_source_289_ = v_source_295_;
v_target_290_ = v_target_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object* v_data_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_nbuckets_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_301_ = lean_array_get_size(v_data_300_);
v___x_302_ = lean_unsigned_to_nat(2u);
v_nbuckets_303_ = lean_nat_mul(v___x_301_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_box(0);
v___x_306_ = lean_mk_array(v_nbuckets_303_, v___x_305_);
v___x_307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v___x_304_, v_data_300_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object* v_m_308_, lean_object* v_a_309_, lean_object* v_b_310_){
_start:
{
lean_object* v_size_311_; lean_object* v_buckets_312_; lean_object* v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v_bkt_326_; uint8_t v___x_327_; 
v_size_311_ = lean_ctor_get(v_m_308_, 0);
v_buckets_312_ = lean_ctor_get(v_m_308_, 1);
v___x_313_ = lean_array_get_size(v_buckets_312_);
v___x_314_ = l_Lean_Expr_hash(v_a_309_);
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_313_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v_bkt_326_ = lean_array_uget_borrowed(v_buckets_312_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_309_, v_bkt_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_348_; 
lean_inc_ref(v_buckets_312_);
lean_inc(v_size_311_);
v_isSharedCheck_348_ = !lean_is_exclusive(v_m_308_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; 
v_unused_349_ = lean_ctor_get(v_m_308_, 1);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_m_308_, 0);
lean_dec(v_unused_350_);
v___x_329_ = v_m_308_;
v_isShared_330_ = v_isSharedCheck_348_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_m_308_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_348_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v_size_x27_332_; lean_object* v___x_333_; lean_object* v_buckets_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v_size_x27_332_ = lean_nat_add(v_size_311_, v___x_331_);
lean_dec(v_size_311_);
lean_inc(v_bkt_326_);
v___x_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_333_, 0, v_a_309_);
lean_ctor_set(v___x_333_, 1, v_b_310_);
lean_ctor_set(v___x_333_, 2, v_bkt_326_);
v_buckets_x27_334_ = lean_array_uset(v_buckets_312_, v___x_325_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(4u);
v___x_336_ = lean_nat_mul(v_size_x27_332_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_div(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_array_get_size(v_buckets_x27_334_);
v___x_340_ = lean_nat_dec_le(v___x_338_, v___x_339_);
lean_dec(v___x_338_);
if (v___x_340_ == 0)
{
lean_object* v_val_341_; lean_object* v___x_343_; 
v_val_341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_buckets_x27_334_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_val_341_);
lean_ctor_set(v___x_329_, 0, v_size_x27_332_);
v___x_343_ = v___x_329_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_val_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_buckets_x27_334_);
lean_ctor_set(v___x_329_, 0, v_size_x27_332_);
v___x_346_ = v___x_329_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_buckets_x27_334_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_dec(v_b_310_);
lean_dec_ref(v_a_309_);
return v_m_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object* v_x_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_d_354_; lean_object* v_b_355_; lean_object* v___y_356_; 
switch(lean_obj_tag(v_x_351_))
{
case 11:
{
lean_object* v_struct_359_; lean_object* v___x_360_; 
v_struct_359_ = lean_ctor_get(v_x_351_, 2);
lean_inc_ref(v_struct_359_);
lean_dec_ref(v_x_351_);
v___x_360_ = l_Lean_CollectLevelParams_visitExpr(v_struct_359_, v_a_352_);
return v___x_360_;
}
case 7:
{
lean_object* v_binderType_361_; lean_object* v_body_362_; 
v_binderType_361_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_binderType_361_);
v_body_362_ = lean_ctor_get(v_x_351_, 2);
lean_inc_ref(v_body_362_);
lean_dec_ref(v_x_351_);
v_d_354_ = v_binderType_361_;
v_b_355_ = v_body_362_;
v___y_356_ = v_a_352_;
goto v___jp_353_;
}
case 6:
{
lean_object* v_binderType_363_; lean_object* v_body_364_; 
v_binderType_363_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_binderType_363_);
v_body_364_ = lean_ctor_get(v_x_351_, 2);
lean_inc_ref(v_body_364_);
lean_dec_ref(v_x_351_);
v_d_354_ = v_binderType_363_;
v_b_355_ = v_body_364_;
v___y_356_ = v_a_352_;
goto v___jp_353_;
}
case 8:
{
lean_object* v_type_365_; lean_object* v_value_366_; lean_object* v_body_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_type_365_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_type_365_);
v_value_366_ = lean_ctor_get(v_x_351_, 2);
lean_inc_ref(v_value_366_);
v_body_367_ = lean_ctor_get(v_x_351_, 3);
lean_inc_ref(v_body_367_);
lean_dec_ref(v_x_351_);
v___x_368_ = l_Lean_CollectLevelParams_visitExpr(v_type_365_, v_a_352_);
v___x_369_ = l_Lean_CollectLevelParams_visitExpr(v_value_366_, v___x_368_);
v___x_370_ = l_Lean_CollectLevelParams_visitExpr(v_body_367_, v___x_369_);
return v___x_370_;
}
case 5:
{
lean_object* v_fn_371_; lean_object* v_arg_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_fn_371_ = lean_ctor_get(v_x_351_, 0);
lean_inc_ref(v_fn_371_);
v_arg_372_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_arg_372_);
lean_dec_ref(v_x_351_);
v___x_373_ = l_Lean_CollectLevelParams_visitExpr(v_fn_371_, v_a_352_);
v___x_374_ = l_Lean_CollectLevelParams_visitExpr(v_arg_372_, v___x_373_);
return v___x_374_;
}
case 10:
{
lean_object* v_expr_375_; lean_object* v___x_376_; 
v_expr_375_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_expr_375_);
lean_dec_ref(v_x_351_);
v___x_376_ = l_Lean_CollectLevelParams_visitExpr(v_expr_375_, v_a_352_);
return v___x_376_;
}
case 4:
{
lean_object* v_us_377_; lean_object* v___x_378_; 
v_us_377_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_us_377_);
lean_dec_ref(v_x_351_);
v___x_378_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_a_352_, v_us_377_);
return v___x_378_;
}
case 3:
{
lean_object* v_u_379_; lean_object* v___x_380_; 
v_u_379_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_u_379_);
lean_dec_ref(v_x_351_);
v___x_380_ = l_Lean_CollectLevelParams_visitLevel(v_u_379_, v_a_352_);
return v___x_380_;
}
default: 
{
lean_dec_ref(v_x_351_);
return v_a_352_;
}
}
v___jp_353_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Lean_CollectLevelParams_visitExpr(v_d_354_, v___y_356_);
v___x_358_ = l_Lean_CollectLevelParams_visitExpr(v_b_355_, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object* v_e_381_, lean_object* v_s_382_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = l_Lean_Expr_hasLevelParam(v_e_381_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_e_381_);
return v_s_382_;
}
else
{
lean_object* v_visitedLevel_384_; lean_object* v_visitedExpr_385_; lean_object* v_params_386_; uint8_t v___x_387_; 
v_visitedLevel_384_ = lean_ctor_get(v_s_382_, 0);
v_visitedExpr_385_ = lean_ctor_get(v_s_382_, 1);
v_params_386_ = lean_ctor_get(v_s_382_, 2);
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_visitedExpr_385_, v_e_381_);
if (v___x_387_ == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_397_; 
lean_inc_ref(v_params_386_);
lean_inc_ref(v_visitedExpr_385_);
lean_inc_ref(v_visitedLevel_384_);
v_isSharedCheck_397_ = !lean_is_exclusive(v_s_382_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_398_ = lean_ctor_get(v_s_382_, 2);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_s_382_, 1);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_s_382_, 0);
lean_dec(v_unused_400_);
v___x_389_ = v_s_382_;
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_s_382_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_box(0);
lean_inc_ref(v_e_381_);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_visitedExpr_385_, v_e_381_, v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_visitedLevel_384_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_params_386_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_CollectLevelParams_main(v_e_381_, v___x_394_);
return v___x_395_;
}
}
}
else
{
lean_dec_ref(v_e_381_);
return v_s_382_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object* v_00_u03b2_401_, lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_402_, v_a_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_405_, lean_object* v_m_406_, lean_object* v_a_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(v_00_u03b2_405_, v_m_406_, v_a_407_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_m_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_411_, v_a_412_, v_b_413_);
return v___x_414_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object* v_00_u03b2_415_, lean_object* v_a_416_, lean_object* v_x_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_416_, v_x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object* v_00_u03b2_419_, lean_object* v_a_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(v_00_u03b2_419_, v_a_420_, v_x_421_);
lean_dec(v_x_421_);
lean_dec_ref(v_a_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object* v_00_u03b2_424_, lean_object* v_data_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_data_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_427_, lean_object* v_i_428_, lean_object* v_source_429_, lean_object* v_target_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v_i_428_, v_source_429_, v_target_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_x_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object* v_s_436_, lean_object* v_pre_437_, lean_object* v_i_438_){
_start:
{
lean_object* v_visitedLevel_439_; lean_object* v___x_440_; lean_object* v_v_441_; uint8_t v___x_442_; 
v_visitedLevel_439_ = lean_ctor_get(v_s_436_, 0);
lean_inc(v_i_438_);
lean_inc(v_pre_437_);
v___x_440_ = lean_name_append_index_after(v_pre_437_, v_i_438_);
v_v_441_ = l_Lean_mkLevelParam(v___x_440_);
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_439_, v_v_441_);
if (v___x_442_ == 0)
{
lean_dec(v_i_438_);
lean_dec(v_pre_437_);
return v_v_441_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_v_441_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_i_438_, v___x_443_);
lean_dec(v_i_438_);
v_i_438_ = v___x_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object* v_s_446_, lean_object* v_pre_447_, lean_object* v_i_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_446_, v_pre_447_, v_i_448_);
lean_dec_ref(v_s_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object* v_s_450_, lean_object* v_pre_451_){
_start:
{
lean_object* v_visitedLevel_452_; lean_object* v_v_453_; uint8_t v___x_454_; 
v_visitedLevel_452_ = lean_ctor_get(v_s_450_, 0);
lean_inc(v_pre_451_);
v_v_453_ = l_Lean_mkLevelParam(v_pre_451_);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_452_, v_v_453_);
if (v___x_454_ == 0)
{
lean_dec(v_pre_451_);
return v_v_453_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_v_453_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_450_, v_pre_451_, v___x_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object* v_s_457_, lean_object* v_pre_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_CollectLevelParams_State_getUnusedLevelParam(v_s_457_, v_pre_458_);
lean_dec_ref(v_s_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object* v_s_460_, lean_object* v_e_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_CollectLevelParams_main(v_e_461_, v_s_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object* v_s_463_, lean_object* v_e_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_CollectLevelParams_main(v_e_464_, v_s_463_);
return v___x_465_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
