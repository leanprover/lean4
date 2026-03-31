// Lean compiler output
// Module: Lean.Util.CollectLevelMVars
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__1;
static const lean_array_object l_Lean_CollectLevelMVars_instInhabitedState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__2 = (const lean_object*)&l_Lean_CollectLevelMVars_instInhabitedState___closed__2_value;
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__0, &l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lean_CollectLevelMVars_instInhabitedState___closed__2));
v___x_10_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__1, &l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_ctor_set(v___x_11_, 2, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__3, &l_Lean_CollectLevelMVars_instInhabitedState___closed__3_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3);
return v___x_12_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v_a_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object* v_m_24_, lean_object* v_a_25_){
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
v___x_41_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_25_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(lean_object* v_m_42_, lean_object* v_a_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_42_, v_a_43_);
lean_dec(v_a_43_);
lean_dec_ref(v_m_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_46_, lean_object* v_x_47_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object* v_i_74_, lean_object* v_source_75_, lean_object* v_target_76_){
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
v_target_82_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_76_, v_es_79_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(lean_object* v_data_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_nbuckets_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_87_ = lean_array_get_size(v_data_86_);
v___x_88_ = lean_unsigned_to_nat(2u);
v_nbuckets_89_ = lean_nat_mul(v___x_87_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_box(0);
v___x_92_ = lean_mk_array(v_nbuckets_89_, v___x_91_);
v___x_93_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_90_, v_data_86_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object* v_m_94_, lean_object* v_a_95_, lean_object* v_b_96_){
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
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_95_, v_bkt_112_);
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
v_val_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_120_);
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
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* v_x_137_, lean_object* v_a_138_){
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
v___x_146_ = l_Lean_CollectLevelMVars_visitLevel(v_a_145_, v_a_138_);
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
case 5:
{
lean_object* v_a_151_; lean_object* v_visitedLevel_152_; lean_object* v_visitedExpr_153_; lean_object* v_result_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_a_151_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v_x_137_);
v_visitedLevel_152_ = lean_ctor_get(v_a_138_, 0);
v_visitedExpr_153_ = lean_ctor_get(v_a_138_, 1);
v_result_154_ = lean_ctor_get(v_a_138_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_138_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_a_138_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_result_154_);
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
v___x_158_ = lean_array_push(v_result_154_, v_a_151_);
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
v___x_143_ = l_Lean_CollectLevelMVars_visitLevel(v_u_140_, v___y_142_);
v___x_144_ = l_Lean_CollectLevelMVars_visitLevel(v_v_141_, v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* v_u_163_, lean_object* v_s_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Level_hasMVar(v_u_163_);
if (v___x_165_ == 0)
{
lean_dec(v_u_163_);
return v_s_164_;
}
else
{
lean_object* v_visitedLevel_166_; lean_object* v_visitedExpr_167_; lean_object* v_result_168_; uint8_t v___x_169_; 
v_visitedLevel_166_ = lean_ctor_get(v_s_164_, 0);
v_visitedExpr_167_ = lean_ctor_get(v_s_164_, 1);
v_result_168_ = lean_ctor_get(v_s_164_, 2);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_166_, v_u_163_);
if (v___x_169_ == 0)
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
lean_inc_ref(v_result_168_);
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
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_166_, v_u_163_, v___x_173_);
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
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_result_168_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_CollectLevelMVars_collect(v_u_163_, v___x_176_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object* v_00_u03b2_183_, lean_object* v_m_184_, lean_object* v_a_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_184_, v_a_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(v_00_u03b2_187_, v_m_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_m_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object* v_00_u03b2_192_, lean_object* v_m_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_193_, v_a_194_, v_b_195_);
return v___x_196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_197_, lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_198_, v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_201_, v_a_202_, v_x_203_);
lean_dec(v_x_203_);
lean_dec(v_a_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_206_, lean_object* v_data_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_data_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_209_, lean_object* v_i_210_, lean_object* v_source_211_, lean_object* v_target_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_210_, v_source_211_, v_target_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
return v_x_218_;
}
else
{
lean_object* v_key_220_; lean_object* v_value_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_245_; 
v_key_220_ = lean_ctor_get(v_x_219_, 0);
v_value_221_ = lean_ctor_get(v_x_219_, 1);
v_tail_222_ = lean_ctor_get(v_x_219_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_245_ == 0)
{
v___x_224_ = v_x_219_;
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_value_221_);
lean_inc(v_key_220_);
lean_dec(v_x_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_226_ = lean_array_get_size(v_x_218_);
v___x_227_ = l_Lean_Expr_hash(v_key_220_);
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___x_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___x_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_226_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_x_218_, v___x_238_);
lean_inc(v___x_239_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 2, v___x_239_);
v___x_241_ = v___x_224_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_key_220_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_value_221_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_uset(v_x_218_, v___x_238_, v___x_241_);
v_x_218_ = v___x_242_;
v_x_219_ = v_tail_222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(lean_object* v_i_246_, lean_object* v_source_247_, lean_object* v_target_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_source_247_);
v___x_250_ = lean_nat_dec_lt(v_i_246_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v_source_247_);
lean_dec(v_i_246_);
return v_target_248_;
}
else
{
lean_object* v_es_251_; lean_object* v___x_252_; lean_object* v_source_253_; lean_object* v_target_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_es_251_ = lean_array_fget(v_source_247_, v_i_246_);
v___x_252_ = lean_box(0);
v_source_253_ = lean_array_fset(v_source_247_, v_i_246_, v___x_252_);
v_target_254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_target_248_, v_es_251_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_i_246_, v___x_255_);
lean_dec(v_i_246_);
v_i_246_ = v___x_256_;
v_source_247_ = v_source_253_;
v_target_248_ = v_target_254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object* v_data_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_nbuckets_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_259_ = lean_array_get_size(v_data_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v_nbuckets_261_ = lean_nat_mul(v___x_259_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_box(0);
v___x_264_ = lean_mk_array(v_nbuckets_261_, v___x_263_);
v___x_265_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v___x_262_, v_data_258_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object* v_a_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
uint8_t v___x_268_; 
v___x_268_ = 0;
return v___x_268_;
}
else
{
lean_object* v_key_269_; lean_object* v_tail_270_; uint8_t v___x_271_; 
v_key_269_ = lean_ctor_get(v_x_267_, 0);
v_tail_270_ = lean_ctor_get(v_x_267_, 2);
v___x_271_ = lean_expr_eqv(v_key_269_, v_a_266_);
if (v___x_271_ == 0)
{
v_x_267_ = v_tail_270_;
goto _start;
}
else
{
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_273_, v_x_274_);
lean_dec(v_x_274_);
lean_dec_ref(v_a_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_size_280_; lean_object* v_buckets_281_; lean_object* v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v_fold_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v_bkt_295_; uint8_t v___x_296_; 
v_size_280_ = lean_ctor_get(v_m_277_, 0);
v_buckets_281_ = lean_ctor_get(v_m_277_, 1);
v___x_282_ = lean_array_get_size(v_buckets_281_);
v___x_283_ = l_Lean_Expr_hash(v_a_278_);
v___x_284_ = 32ULL;
v___x_285_ = lean_uint64_shift_right(v___x_283_, v___x_284_);
v_fold_286_ = lean_uint64_xor(v___x_283_, v___x_285_);
v___x_287_ = 16ULL;
v___x_288_ = lean_uint64_shift_right(v_fold_286_, v___x_287_);
v___x_289_ = lean_uint64_xor(v_fold_286_, v___x_288_);
v___x_290_ = lean_uint64_to_usize(v___x_289_);
v___x_291_ = lean_usize_of_nat(v___x_282_);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_sub(v___x_291_, v___x_292_);
v___x_294_ = lean_usize_land(v___x_290_, v___x_293_);
v_bkt_295_ = lean_array_uget_borrowed(v_buckets_281_, v___x_294_);
v___x_296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_278_, v_bkt_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_buckets_281_);
lean_inc(v_size_280_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_m_277_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_318_ = lean_ctor_get(v_m_277_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_m_277_, 0);
lean_dec(v_unused_319_);
v___x_298_ = v_m_277_;
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_m_277_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_317_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v_size_x27_301_; lean_object* v___x_302_; lean_object* v_buckets_x27_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v_size_x27_301_ = lean_nat_add(v_size_280_, v___x_300_);
lean_dec(v_size_280_);
lean_inc(v_bkt_295_);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v_a_278_);
lean_ctor_set(v___x_302_, 1, v_b_279_);
lean_ctor_set(v___x_302_, 2, v_bkt_295_);
v_buckets_x27_303_ = lean_array_uset(v_buckets_281_, v___x_294_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(4u);
v___x_305_ = lean_nat_mul(v_size_x27_301_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_nat_div(v___x_305_, v___x_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_array_get_size(v_buckets_x27_303_);
v___x_309_ = lean_nat_dec_le(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
if (v___x_309_ == 0)
{
lean_object* v_val_310_; lean_object* v___x_312_; 
v_val_310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_buckets_x27_303_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_val_310_);
lean_ctor_set(v___x_298_, 0, v_size_x27_301_);
v___x_312_ = v___x_298_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_size_x27_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_val_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_buckets_x27_303_);
lean_ctor_set(v___x_298_, 0, v_size_x27_301_);
v___x_315_ = v___x_298_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_x27_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_buckets_x27_303_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_dec(v_b_279_);
lean_dec_ref(v_a_278_);
return v_m_277_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object* v_m_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_buckets_322_; lean_object* v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v_fold_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_buckets_322_ = lean_ctor_get(v_m_320_, 1);
v___x_323_ = lean_array_get_size(v_buckets_322_);
v___x_324_ = l_Lean_Expr_hash(v_a_321_);
v___x_325_ = 32ULL;
v___x_326_ = lean_uint64_shift_right(v___x_324_, v___x_325_);
v_fold_327_ = lean_uint64_xor(v___x_324_, v___x_326_);
v___x_328_ = 16ULL;
v___x_329_ = lean_uint64_shift_right(v_fold_327_, v___x_328_);
v___x_330_ = lean_uint64_xor(v_fold_327_, v___x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = lean_usize_of_nat(v___x_323_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_sub(v___x_332_, v___x_333_);
v___x_335_ = lean_usize_land(v___x_331_, v___x_334_);
v___x_336_ = lean_array_uget_borrowed(v_buckets_322_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_321_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object* v_m_338_, lean_object* v_a_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_338_, v_a_339_);
lean_dec_ref(v_a_339_);
lean_dec_ref(v_m_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
return v_x_342_;
}
else
{
lean_object* v_head_344_; lean_object* v_tail_345_; lean_object* v___x_346_; 
v_head_344_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_head_344_);
v_tail_345_ = lean_ctor_get(v_x_343_, 1);
lean_inc(v_tail_345_);
lean_dec_ref(v_x_343_);
v___x_346_ = l_Lean_CollectLevelMVars_visitLevel(v_head_344_, v_x_342_);
v_x_342_ = v___x_346_;
v_x_343_ = v_tail_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* v_x_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_d_351_; lean_object* v_b_352_; lean_object* v___y_353_; 
switch(lean_obj_tag(v_x_348_))
{
case 11:
{
lean_object* v_struct_356_; lean_object* v___x_357_; 
v_struct_356_ = lean_ctor_get(v_x_348_, 2);
lean_inc_ref(v_struct_356_);
lean_dec_ref(v_x_348_);
v___x_357_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_356_, v_a_349_);
return v___x_357_;
}
case 7:
{
lean_object* v_binderType_358_; lean_object* v_body_359_; 
v_binderType_358_ = lean_ctor_get(v_x_348_, 1);
lean_inc_ref(v_binderType_358_);
v_body_359_ = lean_ctor_get(v_x_348_, 2);
lean_inc_ref(v_body_359_);
lean_dec_ref(v_x_348_);
v_d_351_ = v_binderType_358_;
v_b_352_ = v_body_359_;
v___y_353_ = v_a_349_;
goto v___jp_350_;
}
case 6:
{
lean_object* v_binderType_360_; lean_object* v_body_361_; 
v_binderType_360_ = lean_ctor_get(v_x_348_, 1);
lean_inc_ref(v_binderType_360_);
v_body_361_ = lean_ctor_get(v_x_348_, 2);
lean_inc_ref(v_body_361_);
lean_dec_ref(v_x_348_);
v_d_351_ = v_binderType_360_;
v_b_352_ = v_body_361_;
v___y_353_ = v_a_349_;
goto v___jp_350_;
}
case 8:
{
lean_object* v_type_362_; lean_object* v_value_363_; lean_object* v_body_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_type_362_ = lean_ctor_get(v_x_348_, 1);
lean_inc_ref(v_type_362_);
v_value_363_ = lean_ctor_get(v_x_348_, 2);
lean_inc_ref(v_value_363_);
v_body_364_ = lean_ctor_get(v_x_348_, 3);
lean_inc_ref(v_body_364_);
lean_dec_ref(v_x_348_);
v___x_365_ = l_Lean_CollectLevelMVars_visitExpr(v_type_362_, v_a_349_);
v___x_366_ = l_Lean_CollectLevelMVars_visitExpr(v_value_363_, v___x_365_);
v___x_367_ = l_Lean_CollectLevelMVars_visitExpr(v_body_364_, v___x_366_);
return v___x_367_;
}
case 5:
{
lean_object* v_fn_368_; lean_object* v_arg_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_fn_368_ = lean_ctor_get(v_x_348_, 0);
lean_inc_ref(v_fn_368_);
v_arg_369_ = lean_ctor_get(v_x_348_, 1);
lean_inc_ref(v_arg_369_);
lean_dec_ref(v_x_348_);
v___x_370_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_368_, v_a_349_);
v___x_371_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_369_, v___x_370_);
return v___x_371_;
}
case 10:
{
lean_object* v_expr_372_; lean_object* v___x_373_; 
v_expr_372_ = lean_ctor_get(v_x_348_, 1);
lean_inc_ref(v_expr_372_);
lean_dec_ref(v_x_348_);
v___x_373_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_372_, v_a_349_);
return v___x_373_;
}
case 4:
{
lean_object* v_us_374_; lean_object* v___x_375_; 
v_us_374_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_us_374_);
lean_dec_ref(v_x_348_);
v___x_375_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(v_a_349_, v_us_374_);
return v___x_375_;
}
case 3:
{
lean_object* v_u_376_; lean_object* v___x_377_; 
v_u_376_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_u_376_);
lean_dec_ref(v_x_348_);
v___x_377_ = l_Lean_CollectLevelMVars_visitLevel(v_u_376_, v_a_349_);
return v___x_377_;
}
default: 
{
lean_dec_ref(v_x_348_);
return v_a_349_;
}
}
v___jp_350_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l_Lean_CollectLevelMVars_visitExpr(v_d_351_, v___y_353_);
v___x_355_ = l_Lean_CollectLevelMVars_visitExpr(v_b_352_, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* v_e_378_, lean_object* v_s_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Lean_Expr_hasMVar(v_e_378_);
if (v___x_380_ == 0)
{
lean_dec_ref(v_e_378_);
return v_s_379_;
}
else
{
lean_object* v_visitedLevel_381_; lean_object* v_visitedExpr_382_; lean_object* v_result_383_; uint8_t v___x_384_; 
v_visitedLevel_381_ = lean_ctor_get(v_s_379_, 0);
v_visitedExpr_382_ = lean_ctor_get(v_s_379_, 1);
v_result_383_ = lean_ctor_get(v_s_379_, 2);
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_382_, v_e_378_);
if (v___x_384_ == 0)
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_394_; 
lean_inc_ref(v_result_383_);
lean_inc_ref(v_visitedExpr_382_);
lean_inc_ref(v_visitedLevel_381_);
v_isSharedCheck_394_ = !lean_is_exclusive(v_s_379_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_395_ = lean_ctor_get(v_s_379_, 2);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_s_379_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_s_379_, 0);
lean_dec(v_unused_397_);
v___x_386_ = v_s_379_;
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_s_379_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_388_ = lean_box(0);
lean_inc_ref(v_e_378_);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_382_, v_e_378_, v___x_388_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_visitedLevel_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_result_383_);
v___x_391_ = v_reuseFailAlloc_393_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_CollectLevelMVars_main(v_e_378_, v___x_391_);
return v___x_392_;
}
}
}
else
{
lean_dec_ref(v_e_378_);
return v_s_379_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object* v_00_u03b2_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_399_, v_a_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_402_, lean_object* v_m_403_, lean_object* v_a_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(v_00_u03b2_402_, v_m_403_, v_a_404_);
lean_dec_ref(v_a_404_);
lean_dec_ref(v_m_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_a_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_408_, v_a_409_, v_b_410_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_416_, lean_object* v_a_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(v_00_u03b2_416_, v_a_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_a_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object* v_00_u03b2_421_, lean_object* v_data_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_data_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_424_, lean_object* v_i_425_, lean_object* v_source_426_, lean_object* v_target_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v_i_425_, v_source_426_, v_target_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_x_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object* v_s_433_, lean_object* v_e_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_CollectLevelMVars_main(v_e_434_, v_s_433_);
return v___x_435_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelMVars_instInhabitedState = _init_l_Lean_CollectLevelMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLevelMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLevelMVars(builtin);
}
#ifdef __cplusplus
}
#endif
