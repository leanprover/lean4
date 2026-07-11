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
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
return v_x_13_;
}
else
{
lean_object* v_key_15_; lean_object* v_value_16_; lean_object* v_tail_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_40_; 
v_key_15_ = lean_ctor_get(v_x_14_, 0);
v_value_16_ = lean_ctor_get(v_x_14_, 1);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_40_ == 0)
{
v___x_19_ = v_x_14_;
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_tail_17_);
lean_inc(v_value_16_);
lean_inc(v_key_15_);
lean_dec(v_x_14_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v_fold_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_21_ = lean_array_get_size(v_x_13_);
v___x_22_ = l_Lean_Level_hash(v_key_15_);
v___x_23_ = 32ULL;
v___x_24_ = lean_uint64_shift_right(v___x_22_, v___x_23_);
v_fold_25_ = lean_uint64_xor(v___x_22_, v___x_24_);
v___x_26_ = 16ULL;
v___x_27_ = lean_uint64_shift_right(v_fold_25_, v___x_26_);
v___x_28_ = lean_uint64_xor(v_fold_25_, v___x_27_);
v___x_29_ = lean_uint64_to_usize(v___x_28_);
v___x_30_ = lean_usize_of_nat(v___x_21_);
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_sub(v___x_30_, v___x_31_);
v___x_33_ = lean_usize_land(v___x_29_, v___x_32_);
v___x_34_ = lean_array_uget_borrowed(v_x_13_, v___x_33_);
lean_inc(v___x_34_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v___x_34_);
v___x_36_ = v___x_19_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_key_15_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_value_16_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v___x_34_);
v___x_36_ = v_reuseFailAlloc_39_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; 
v___x_37_ = lean_array_uset(v_x_13_, v___x_33_, v___x_36_);
v_x_13_ = v___x_37_;
v_x_14_ = v_tail_17_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3___redArg(lean_object* v_i_41_, lean_object* v_source_42_, lean_object* v_target_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_array_get_size(v_source_42_);
v___x_45_ = lean_nat_dec_lt(v_i_41_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec_ref(v_source_42_);
lean_dec(v_i_41_);
return v_target_43_;
}
else
{
lean_object* v_es_46_; lean_object* v___x_47_; lean_object* v_source_48_; lean_object* v_target_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_es_46_ = lean_array_fget(v_source_42_, v_i_41_);
v___x_47_ = lean_box(0);
v_source_48_ = lean_array_fset(v_source_42_, v_i_41_, v___x_47_);
v_target_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(v_target_43_, v_es_46_);
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_i_41_, v___x_50_);
lean_dec(v_i_41_);
v_i_41_ = v___x_51_;
v_source_42_ = v_source_48_;
v_target_43_ = v_target_49_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2___redArg(lean_object* v_data_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_nbuckets_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_54_ = lean_array_get_size(v_data_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v_nbuckets_56_ = lean_nat_mul(v___x_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_box(0);
v___x_59_ = lean_mk_array(v_nbuckets_56_, v___x_58_);
v___x_60_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3___redArg(v___x_57_, v_data_53_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
else
{
lean_object* v_key_64_; lean_object* v_tail_65_; uint8_t v___x_66_; 
v_key_64_ = lean_ctor_get(v_x_62_, 0);
v_tail_65_ = lean_ctor_get(v_x_62_, 2);
v___x_66_ = lean_level_eq(v_key_64_, v_a_61_);
if (v___x_66_ == 0)
{
v_x_62_ = v_tail_65_;
goto _start;
}
else
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_a_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object* v_m_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v_size_75_; lean_object* v_buckets_76_; lean_object* v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v_fold_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v_bkt_90_; uint8_t v___x_91_; 
v_size_75_ = lean_ctor_get(v_m_72_, 0);
v_buckets_76_ = lean_ctor_get(v_m_72_, 1);
v___x_77_ = lean_array_get_size(v_buckets_76_);
v___x_78_ = l_Lean_Level_hash(v_a_73_);
v___x_79_ = 32ULL;
v___x_80_ = lean_uint64_shift_right(v___x_78_, v___x_79_);
v_fold_81_ = lean_uint64_xor(v___x_78_, v___x_80_);
v___x_82_ = 16ULL;
v___x_83_ = lean_uint64_shift_right(v_fold_81_, v___x_82_);
v___x_84_ = lean_uint64_xor(v_fold_81_, v___x_83_);
v___x_85_ = lean_uint64_to_usize(v___x_84_);
v___x_86_ = lean_usize_of_nat(v___x_77_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_sub(v___x_86_, v___x_87_);
v___x_89_ = lean_usize_land(v___x_85_, v___x_88_);
v_bkt_90_ = lean_array_uget_borrowed(v_buckets_76_, v___x_89_);
v___x_91_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_73_, v_bkt_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_112_; 
lean_inc_ref(v_buckets_76_);
lean_inc(v_size_75_);
v_isSharedCheck_112_ = !lean_is_exclusive(v_m_72_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; lean_object* v_unused_114_; 
v_unused_113_ = lean_ctor_get(v_m_72_, 1);
lean_dec(v_unused_113_);
v_unused_114_ = lean_ctor_get(v_m_72_, 0);
lean_dec(v_unused_114_);
v___x_93_ = v_m_72_;
v_isShared_94_ = v_isSharedCheck_112_;
goto v_resetjp_92_;
}
else
{
lean_dec(v_m_72_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_112_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v_size_x27_96_; lean_object* v___x_97_; lean_object* v_buckets_x27_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v_size_x27_96_ = lean_nat_add(v_size_75_, v___x_95_);
lean_dec(v_size_75_);
lean_inc(v_bkt_90_);
v___x_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_97_, 0, v_a_73_);
lean_ctor_set(v___x_97_, 1, v_b_74_);
lean_ctor_set(v___x_97_, 2, v_bkt_90_);
v_buckets_x27_98_ = lean_array_uset(v_buckets_76_, v___x_89_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(4u);
v___x_100_ = lean_nat_mul(v_size_x27_96_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(3u);
v___x_102_ = lean_nat_div(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_array_get_size(v_buckets_x27_98_);
v___x_104_ = lean_nat_dec_le(v___x_102_, v___x_103_);
lean_dec(v___x_102_);
if (v___x_104_ == 0)
{
lean_object* v_val_105_; lean_object* v___x_107_; 
v_val_105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2___redArg(v_buckets_x27_98_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v_val_105_);
lean_ctor_set(v___x_93_, 0, v_size_x27_96_);
v___x_107_ = v___x_93_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_size_x27_96_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_val_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
else
{
lean_object* v___x_110_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v_buckets_x27_98_);
lean_ctor_set(v___x_93_, 0, v_size_x27_96_);
v___x_110_ = v___x_93_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_size_x27_96_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_buckets_x27_98_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_dec(v_b_74_);
lean_dec(v_a_73_);
return v_m_72_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_buckets_117_; lean_object* v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_buckets_117_ = lean_ctor_get(v_m_115_, 1);
v___x_118_ = lean_array_get_size(v_buckets_117_);
v___x_119_ = l_Lean_Level_hash(v_a_116_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_118_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_array_uget_borrowed(v_buckets_117_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_116_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg___boxed(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_m_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* v_u_137_, lean_object* v_s_138_){
_start:
{
uint8_t v___y_140_; uint8_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = l_Lean_Level_hasParam(v_u_137_);
v___x_155_ = lean_bool_not(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v_visitedLevel_156_; uint8_t v___x_157_; 
v_visitedLevel_156_ = lean_ctor_get(v_s_138_, 0);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_156_, v_u_137_);
v___y_140_ = v___x_157_;
goto v___jp_139_;
}
else
{
v___y_140_ = v___x_155_;
goto v___jp_139_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
lean_object* v_visitedLevel_141_; lean_object* v_visitedExpr_142_; lean_object* v_params_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_visitedLevel_141_ = lean_ctor_get(v_s_138_, 0);
v_visitedExpr_142_ = lean_ctor_get(v_s_138_, 1);
v_params_143_ = lean_ctor_get(v_s_138_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_s_138_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v_s_138_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_params_143_);
lean_inc(v_visitedExpr_142_);
lean_inc(v_visitedLevel_141_);
lean_dec(v_s_138_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
lean_inc(v_u_137_);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_141_, v_u_137_, v___x_147_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_148_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_visitedExpr_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_params_143_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_CollectLevelParams_collect(v_u_137_, v___x_150_);
return v___x_151_;
}
}
}
else
{
lean_dec(v_u_137_);
return v_s_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object* v_x_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_u_161_; lean_object* v_v_162_; lean_object* v___y_163_; 
switch(lean_obj_tag(v_x_158_))
{
case 1:
{
lean_object* v_a_166_; lean_object* v___x_167_; 
v_a_166_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v_x_158_, 1);
v___x_167_ = l_Lean_CollectLevelParams_visitLevel(v_a_166_, v_a_159_);
return v___x_167_;
}
case 2:
{
lean_object* v_a_168_; lean_object* v_a_169_; 
v_a_168_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_168_);
v_a_169_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_a_169_);
lean_dec_ref_known(v_x_158_, 2);
v_u_161_ = v_a_168_;
v_v_162_ = v_a_169_;
v___y_163_ = v_a_159_;
goto v___jp_160_;
}
case 3:
{
lean_object* v_a_170_; lean_object* v_a_171_; 
v_a_170_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_170_);
v_a_171_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_a_171_);
lean_dec_ref_known(v_x_158_, 2);
v_u_161_ = v_a_170_;
v_v_162_ = v_a_171_;
v___y_163_ = v_a_159_;
goto v___jp_160_;
}
case 4:
{
lean_object* v_a_172_; lean_object* v_visitedLevel_173_; lean_object* v_visitedExpr_174_; lean_object* v_params_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_172_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v_x_158_, 1);
v_visitedLevel_173_ = lean_ctor_get(v_a_159_, 0);
v_visitedExpr_174_ = lean_ctor_get(v_a_159_, 1);
v_params_175_ = lean_ctor_get(v_a_159_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_a_159_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_params_175_);
lean_inc(v_visitedExpr_174_);
lean_inc(v_visitedLevel_173_);
lean_dec(v_a_159_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_array_push(v_params_175_, v_a_172_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_visitedLevel_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_visitedExpr_174_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
default: 
{
lean_dec(v_x_158_);
return v_a_159_;
}
}
v___jp_160_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l_Lean_CollectLevelParams_visitLevel(v_u_161_, v___y_163_);
v___x_165_ = l_Lean_CollectLevelParams_visitLevel(v_v_162_, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_185_, v_a_186_, v_b_187_);
return v___x_188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object* v_00_u03b2_189_, lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_190_, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___boxed(lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1(v_00_u03b2_193_, v_m_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_m_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_202_, lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(v_00_u03b2_202_, v_a_203_, v_x_204_);
lean_dec(v_x_204_);
lean_dec(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2(lean_object* v_00_u03b2_207_, lean_object* v_data_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2___redArg(v_data_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_210_, lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3___redArg(v_i_211_, v_source_212_, v_target_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_223_; 
v_head_221_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_head_221_);
v_tail_222_ = lean_ctor_get(v_x_220_, 1);
lean_inc(v_tail_222_);
lean_dec_ref_known(v_x_220_, 2);
v___x_223_ = l_Lean_CollectLevelParams_visitLevel(v_head_221_, v_x_219_);
v_x_219_ = v___x_223_;
v_x_220_ = v_tail_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object* v_us_225_, lean_object* v_s_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_s_226_, v_us_225_);
return v___x_227_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
else
{
lean_object* v_key_231_; lean_object* v_tail_232_; uint8_t v___x_233_; 
v_key_231_ = lean_ctor_get(v_x_229_, 0);
v_tail_232_ = lean_ctor_get(v_x_229_, 2);
v___x_233_ = lean_expr_eqv(v_key_231_, v_a_228_);
if (v___x_233_ == 0)
{
v_x_229_ = v_tail_232_;
goto _start;
}
else
{
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object* v_a_235_, lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_235_, v_x_236_);
lean_dec(v_x_236_);
lean_dec_ref(v_a_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_buckets_241_; lean_object* v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v_fold_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_buckets_241_ = lean_ctor_get(v_m_239_, 1);
v___x_242_ = lean_array_get_size(v_buckets_241_);
v___x_243_ = l_Lean_Expr_hash(v_a_240_);
v___x_244_ = 32ULL;
v___x_245_ = lean_uint64_shift_right(v___x_243_, v___x_244_);
v_fold_246_ = lean_uint64_xor(v___x_243_, v___x_245_);
v___x_247_ = 16ULL;
v___x_248_ = lean_uint64_shift_right(v_fold_246_, v___x_247_);
v___x_249_ = lean_uint64_xor(v_fold_246_, v___x_248_);
v___x_250_ = lean_uint64_to_usize(v___x_249_);
v___x_251_ = lean_usize_of_nat(v___x_242_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_sub(v___x_251_, v___x_252_);
v___x_254_ = lean_usize_land(v___x_250_, v___x_253_);
v___x_255_ = lean_array_uget_borrowed(v_buckets_241_, v___x_254_);
v___x_256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_240_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object* v_m_257_, lean_object* v_a_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_257_, v_a_258_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_m_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
return v_x_261_;
}
else
{
lean_object* v_key_263_; lean_object* v_value_264_; lean_object* v_tail_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_288_; 
v_key_263_ = lean_ctor_get(v_x_262_, 0);
v_value_264_ = lean_ctor_get(v_x_262_, 1);
v_tail_265_ = lean_ctor_get(v_x_262_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_288_ == 0)
{
v___x_267_ = v_x_262_;
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_tail_265_);
lean_inc(v_value_264_);
lean_inc(v_key_263_);
lean_dec(v_x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v_fold_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_269_ = lean_array_get_size(v_x_261_);
v___x_270_ = l_Lean_Expr_hash(v_key_263_);
v___x_271_ = 32ULL;
v___x_272_ = lean_uint64_shift_right(v___x_270_, v___x_271_);
v_fold_273_ = lean_uint64_xor(v___x_270_, v___x_272_);
v___x_274_ = 16ULL;
v___x_275_ = lean_uint64_shift_right(v_fold_273_, v___x_274_);
v___x_276_ = lean_uint64_xor(v_fold_273_, v___x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = lean_usize_of_nat(v___x_269_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_sub(v___x_278_, v___x_279_);
v___x_281_ = lean_usize_land(v___x_277_, v___x_280_);
v___x_282_ = lean_array_uget_borrowed(v_x_261_, v___x_281_);
lean_inc(v___x_282_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 2, v___x_282_);
v___x_284_ = v___x_267_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_key_263_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_value_264_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v___x_282_);
v___x_284_ = v_reuseFailAlloc_287_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_uset(v_x_261_, v___x_281_, v___x_284_);
v_x_261_ = v___x_285_;
v_x_262_ = v_tail_265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(lean_object* v_i_289_, lean_object* v_source_290_, lean_object* v_target_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_source_290_);
v___x_293_ = lean_nat_dec_lt(v_i_289_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v_source_290_);
lean_dec(v_i_289_);
return v_target_291_;
}
else
{
lean_object* v_es_294_; lean_object* v___x_295_; lean_object* v_source_296_; lean_object* v_target_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_es_294_ = lean_array_fget(v_source_290_, v_i_289_);
v___x_295_ = lean_box(0);
v_source_296_ = lean_array_fset(v_source_290_, v_i_289_, v___x_295_);
v_target_297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_target_291_, v_es_294_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_289_, v___x_298_);
lean_dec(v_i_289_);
v_i_289_ = v___x_299_;
v_source_290_ = v_source_296_;
v_target_291_ = v_target_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object* v_data_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_nbuckets_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_302_ = lean_array_get_size(v_data_301_);
v___x_303_ = lean_unsigned_to_nat(2u);
v_nbuckets_304_ = lean_nat_mul(v___x_302_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_box(0);
v___x_307_ = lean_mk_array(v_nbuckets_304_, v___x_306_);
v___x_308_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v___x_305_, v_data_301_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object* v_m_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
lean_object* v_size_312_; lean_object* v_buckets_313_; lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v_bkt_327_; uint8_t v___x_328_; 
v_size_312_ = lean_ctor_get(v_m_309_, 0);
v_buckets_313_ = lean_ctor_get(v_m_309_, 1);
v___x_314_ = lean_array_get_size(v_buckets_313_);
v___x_315_ = l_Lean_Expr_hash(v_a_310_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v_bkt_327_ = lean_array_uget_borrowed(v_buckets_313_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_310_, v_bkt_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_349_; 
lean_inc_ref(v_buckets_313_);
lean_inc(v_size_312_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_m_309_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_350_ = lean_ctor_get(v_m_309_, 1);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_m_309_, 0);
lean_dec(v_unused_351_);
v___x_330_ = v_m_309_;
v_isShared_331_ = v_isSharedCheck_349_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_m_309_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_349_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_size_x27_333_; lean_object* v___x_334_; lean_object* v_buckets_x27_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v_size_x27_333_ = lean_nat_add(v_size_312_, v___x_332_);
lean_dec(v_size_312_);
lean_inc(v_bkt_327_);
v___x_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_334_, 0, v_a_310_);
lean_ctor_set(v___x_334_, 1, v_b_311_);
lean_ctor_set(v___x_334_, 2, v_bkt_327_);
v_buckets_x27_335_ = lean_array_uset(v_buckets_313_, v___x_326_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(4u);
v___x_337_ = lean_nat_mul(v_size_x27_333_, v___x_336_);
v___x_338_ = lean_unsigned_to_nat(3u);
v___x_339_ = lean_nat_div(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_array_get_size(v_buckets_x27_335_);
v___x_341_ = lean_nat_dec_le(v___x_339_, v___x_340_);
lean_dec(v___x_339_);
if (v___x_341_ == 0)
{
lean_object* v_val_342_; lean_object* v___x_344_; 
v_val_342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_buckets_x27_335_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_val_342_);
lean_ctor_set(v___x_330_, 0, v_size_x27_333_);
v___x_344_ = v___x_330_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_val_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_buckets_x27_335_);
lean_ctor_set(v___x_330_, 0, v_size_x27_333_);
v___x_347_ = v___x_330_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_size_x27_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_buckets_x27_335_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_dec(v_b_311_);
lean_dec_ref(v_a_310_);
return v_m_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object* v_x_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_d_355_; lean_object* v_b_356_; lean_object* v___y_357_; 
switch(lean_obj_tag(v_x_352_))
{
case 11:
{
lean_object* v_struct_360_; lean_object* v___x_361_; 
v_struct_360_ = lean_ctor_get(v_x_352_, 2);
lean_inc_ref(v_struct_360_);
lean_dec_ref_known(v_x_352_, 3);
v___x_361_ = l_Lean_CollectLevelParams_visitExpr(v_struct_360_, v_a_353_);
return v___x_361_;
}
case 7:
{
lean_object* v_binderType_362_; lean_object* v_body_363_; 
v_binderType_362_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_binderType_362_);
v_body_363_ = lean_ctor_get(v_x_352_, 2);
lean_inc_ref(v_body_363_);
lean_dec_ref_known(v_x_352_, 3);
v_d_355_ = v_binderType_362_;
v_b_356_ = v_body_363_;
v___y_357_ = v_a_353_;
goto v___jp_354_;
}
case 6:
{
lean_object* v_binderType_364_; lean_object* v_body_365_; 
v_binderType_364_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_binderType_364_);
v_body_365_ = lean_ctor_get(v_x_352_, 2);
lean_inc_ref(v_body_365_);
lean_dec_ref_known(v_x_352_, 3);
v_d_355_ = v_binderType_364_;
v_b_356_ = v_body_365_;
v___y_357_ = v_a_353_;
goto v___jp_354_;
}
case 8:
{
lean_object* v_type_366_; lean_object* v_value_367_; lean_object* v_body_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_type_366_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_type_366_);
v_value_367_ = lean_ctor_get(v_x_352_, 2);
lean_inc_ref(v_value_367_);
v_body_368_ = lean_ctor_get(v_x_352_, 3);
lean_inc_ref(v_body_368_);
lean_dec_ref_known(v_x_352_, 4);
v___x_369_ = l_Lean_CollectLevelParams_visitExpr(v_type_366_, v_a_353_);
v___x_370_ = l_Lean_CollectLevelParams_visitExpr(v_value_367_, v___x_369_);
v___x_371_ = l_Lean_CollectLevelParams_visitExpr(v_body_368_, v___x_370_);
return v___x_371_;
}
case 5:
{
lean_object* v_fn_372_; lean_object* v_arg_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_fn_372_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_fn_372_);
v_arg_373_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_arg_373_);
lean_dec_ref_known(v_x_352_, 2);
v___x_374_ = l_Lean_CollectLevelParams_visitExpr(v_fn_372_, v_a_353_);
v___x_375_ = l_Lean_CollectLevelParams_visitExpr(v_arg_373_, v___x_374_);
return v___x_375_;
}
case 10:
{
lean_object* v_expr_376_; lean_object* v___x_377_; 
v_expr_376_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_expr_376_);
lean_dec_ref_known(v_x_352_, 2);
v___x_377_ = l_Lean_CollectLevelParams_visitExpr(v_expr_376_, v_a_353_);
return v___x_377_;
}
case 4:
{
lean_object* v_us_378_; lean_object* v___x_379_; 
v_us_378_ = lean_ctor_get(v_x_352_, 1);
lean_inc(v_us_378_);
lean_dec_ref_known(v_x_352_, 2);
v___x_379_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_a_353_, v_us_378_);
return v___x_379_;
}
case 3:
{
lean_object* v_u_380_; lean_object* v___x_381_; 
v_u_380_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_u_380_);
lean_dec_ref_known(v_x_352_, 1);
v___x_381_ = l_Lean_CollectLevelParams_visitLevel(v_u_380_, v_a_353_);
return v___x_381_;
}
default: 
{
lean_dec_ref(v_x_352_);
return v_a_353_;
}
}
v___jp_354_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_CollectLevelParams_visitExpr(v_d_355_, v___y_357_);
v___x_359_ = l_Lean_CollectLevelParams_visitExpr(v_b_356_, v___x_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object* v_e_382_, lean_object* v_s_383_){
_start:
{
uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = l_Lean_Expr_hasLevelParam(v_e_382_);
v___x_385_ = lean_bool_not(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v_visitedLevel_386_; lean_object* v_visitedExpr_387_; lean_object* v_params_388_; uint8_t v___x_389_; 
v_visitedLevel_386_ = lean_ctor_get(v_s_383_, 0);
v_visitedExpr_387_ = lean_ctor_get(v_s_383_, 1);
v_params_388_ = lean_ctor_get(v_s_383_, 2);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_visitedExpr_387_, v_e_382_);
if (v___x_389_ == 0)
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
lean_inc_ref(v_params_388_);
lean_inc_ref(v_visitedExpr_387_);
lean_inc_ref(v_visitedLevel_386_);
v_isSharedCheck_399_ = !lean_is_exclusive(v_s_383_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_400_ = lean_ctor_get(v_s_383_, 2);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_s_383_, 1);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_s_383_, 0);
lean_dec(v_unused_402_);
v___x_391_ = v_s_383_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_s_383_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_box(0);
lean_inc_ref(v_e_382_);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_visitedExpr_387_, v_e_382_, v___x_393_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_visitedLevel_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_params_388_);
v___x_396_ = v_reuseFailAlloc_398_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_CollectLevelParams_main(v_e_382_, v___x_396_);
return v___x_397_;
}
}
}
else
{
lean_dec_ref(v_e_382_);
return v_s_383_;
}
}
else
{
lean_dec_ref(v_e_382_);
return v_s_383_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object* v_00_u03b2_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_404_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(v_00_u03b2_407_, v_m_408_, v_a_409_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_m_408_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_413_, v_a_414_, v_b_415_);
return v___x_416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object* v_00_u03b2_417_, lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_418_, v_x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object* v_00_u03b2_421_, lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(v_00_u03b2_421_, v_a_422_, v_x_423_);
lean_dec(v_x_423_);
lean_dec_ref(v_a_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object* v_00_u03b2_426_, lean_object* v_data_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_data_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_429_, lean_object* v_i_430_, lean_object* v_source_431_, lean_object* v_target_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v_i_430_, v_source_431_, v_target_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object* v_s_438_, lean_object* v_pre_439_, lean_object* v_i_440_){
_start:
{
lean_object* v_visitedLevel_441_; lean_object* v___x_442_; lean_object* v_v_443_; uint8_t v___x_444_; 
v_visitedLevel_441_ = lean_ctor_get(v_s_438_, 0);
lean_inc(v_i_440_);
lean_inc(v_pre_439_);
v___x_442_ = lean_name_append_index_after(v_pre_439_, v_i_440_);
v_v_443_ = l_Lean_mkLevelParam(v___x_442_);
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_441_, v_v_443_);
if (v___x_444_ == 0)
{
lean_dec(v_i_440_);
lean_dec(v_pre_439_);
return v_v_443_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_v_443_);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_i_440_, v___x_445_);
lean_dec(v_i_440_);
v_i_440_ = v___x_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object* v_s_448_, lean_object* v_pre_449_, lean_object* v_i_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_448_, v_pre_449_, v_i_450_);
lean_dec_ref(v_s_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object* v_s_452_, lean_object* v_pre_453_){
_start:
{
lean_object* v_visitedLevel_454_; lean_object* v_v_455_; uint8_t v___x_456_; 
v_visitedLevel_454_ = lean_ctor_get(v_s_452_, 0);
lean_inc(v_pre_453_);
v_v_455_ = l_Lean_mkLevelParam(v_pre_453_);
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_454_, v_v_455_);
if (v___x_456_ == 0)
{
lean_dec(v_pre_453_);
return v_v_455_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_v_455_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_452_, v_pre_453_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object* v_s_459_, lean_object* v_pre_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_CollectLevelParams_State_getUnusedLevelParam(v_s_459_, v_pre_460_);
lean_dec_ref(v_s_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object* v_s_462_, lean_object* v_e_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_CollectLevelParams_main(v_e_463_, v_s_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object* v_s_465_, lean_object* v_e_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_CollectLevelParams_main(v_e_466_, v_s_465_);
return v___x_467_;
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
