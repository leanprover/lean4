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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_nbuckets_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_87_ = lean_array_get_size(v_data_86_);
v___x_88_ = lean_unsigned_to_nat(2u);
v_nbuckets_89_ = lean_nat_mul(v___x_87_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_box(0);
v___x_92_ = lean_mk_array(v_nbuckets_89_, v___x_91_);
v___x_93_ = lean_array_propagate_mark(v_data_86_, v___x_92_);
v___x_94_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_90_, v_data_86_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object* v_m_95_, lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
lean_object* v_size_98_; lean_object* v_buckets_99_; lean_object* v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v_fold_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v_bkt_113_; uint8_t v___x_114_; 
v_size_98_ = lean_ctor_get(v_m_95_, 0);
v_buckets_99_ = lean_ctor_get(v_m_95_, 1);
v___x_100_ = lean_array_get_size(v_buckets_99_);
v___x_101_ = l_Lean_Level_hash(v_a_96_);
v___x_102_ = 32ULL;
v___x_103_ = lean_uint64_shift_right(v___x_101_, v___x_102_);
v_fold_104_ = lean_uint64_xor(v___x_101_, v___x_103_);
v___x_105_ = 16ULL;
v___x_106_ = lean_uint64_shift_right(v_fold_104_, v___x_105_);
v___x_107_ = lean_uint64_xor(v_fold_104_, v___x_106_);
v___x_108_ = lean_uint64_to_usize(v___x_107_);
v___x_109_ = lean_usize_of_nat(v___x_100_);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_sub(v___x_109_, v___x_110_);
v___x_112_ = lean_usize_land(v___x_108_, v___x_111_);
v_bkt_113_ = lean_array_uget_borrowed(v_buckets_99_, v___x_112_);
v___x_114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_96_, v_bkt_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_buckets_99_);
lean_inc(v_size_98_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_m_95_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_136_ = lean_ctor_get(v_m_95_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_m_95_, 0);
lean_dec(v_unused_137_);
v___x_116_ = v_m_95_;
v_isShared_117_ = v_isSharedCheck_135_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_m_95_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_135_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v_size_x27_119_; lean_object* v___x_120_; lean_object* v_buckets_x27_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v_size_x27_119_ = lean_nat_add(v_size_98_, v___x_118_);
lean_dec(v_size_98_);
lean_inc(v_bkt_113_);
v___x_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_120_, 0, v_a_96_);
lean_ctor_set(v___x_120_, 1, v_b_97_);
lean_ctor_set(v___x_120_, 2, v_bkt_113_);
v_buckets_x27_121_ = lean_array_uset(v_buckets_99_, v___x_112_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(4u);
v___x_123_ = lean_nat_mul(v_size_x27_119_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = lean_nat_div(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_array_get_size(v_buckets_x27_121_);
v___x_127_ = lean_nat_dec_le(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v_val_128_; lean_object* v___x_130_; 
v_val_128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_121_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_val_128_);
lean_ctor_set(v___x_116_, 0, v_size_x27_119_);
v___x_130_ = v___x_116_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_size_x27_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_val_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v___x_133_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_buckets_x27_121_);
lean_ctor_set(v___x_116_, 0, v_size_x27_119_);
v___x_133_ = v___x_116_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_size_x27_119_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_buckets_x27_121_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_dec(v_b_97_);
lean_dec(v_a_96_);
return v_m_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* v_x_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_u_141_; lean_object* v_v_142_; lean_object* v___y_143_; 
switch(lean_obj_tag(v_x_138_))
{
case 1:
{
lean_object* v_a_146_; lean_object* v___x_147_; 
v_a_146_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_146_);
lean_dec_ref_known(v_x_138_, 1);
v___x_147_ = l_Lean_CollectLevelMVars_visitLevel(v_a_146_, v_a_139_);
return v___x_147_;
}
case 2:
{
lean_object* v_a_148_; lean_object* v_a_149_; 
v_a_148_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_148_);
v_a_149_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_a_149_);
lean_dec_ref_known(v_x_138_, 2);
v_u_141_ = v_a_148_;
v_v_142_ = v_a_149_;
v___y_143_ = v_a_139_;
goto v___jp_140_;
}
case 3:
{
lean_object* v_a_150_; lean_object* v_a_151_; 
v_a_150_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_150_);
v_a_151_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_a_151_);
lean_dec_ref_known(v_x_138_, 2);
v_u_141_ = v_a_150_;
v_v_142_ = v_a_151_;
v___y_143_ = v_a_139_;
goto v___jp_140_;
}
case 5:
{
lean_object* v_a_152_; lean_object* v_visitedLevel_153_; lean_object* v_visitedExpr_154_; lean_object* v_result_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_163_; 
v_a_152_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v_x_138_, 1);
v_visitedLevel_153_ = lean_ctor_get(v_a_139_, 0);
v_visitedExpr_154_ = lean_ctor_get(v_a_139_, 1);
v_result_155_ = lean_ctor_get(v_a_139_, 2);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_157_ = v_a_139_;
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_result_155_);
lean_inc(v_visitedExpr_154_);
lean_inc(v_visitedLevel_153_);
lean_dec(v_a_139_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_array_push(v_result_155_, v_a_152_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 2, v___x_159_);
v___x_161_ = v___x_157_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_visitedLevel_153_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_visitedExpr_154_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
default: 
{
lean_dec(v_x_138_);
return v_a_139_;
}
}
v___jp_140_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_Lean_CollectLevelMVars_visitLevel(v_u_141_, v___y_143_);
v___x_145_ = l_Lean_CollectLevelMVars_visitLevel(v_v_142_, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* v_u_164_, lean_object* v_s_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_Level_hasMVar(v_u_164_);
if (v___x_166_ == 0)
{
lean_dec(v_u_164_);
return v_s_165_;
}
else
{
lean_object* v_visitedLevel_167_; lean_object* v_visitedExpr_168_; lean_object* v_result_169_; uint8_t v___x_170_; 
v_visitedLevel_167_ = lean_ctor_get(v_s_165_, 0);
v_visitedExpr_168_ = lean_ctor_get(v_s_165_, 1);
v_result_169_ = lean_ctor_get(v_s_165_, 2);
v___x_170_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_167_, v_u_164_);
if (v___x_170_ == 0)
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
lean_inc_ref(v_result_169_);
lean_inc_ref(v_visitedExpr_168_);
lean_inc_ref(v_visitedLevel_167_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_s_165_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_181_ = lean_ctor_get(v_s_165_, 2);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_s_165_, 1);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_s_165_, 0);
lean_dec(v_unused_183_);
v___x_172_ = v_s_165_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_dec(v_s_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_box(0);
lean_inc(v_u_164_);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_167_, v_u_164_, v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_visitedExpr_168_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_result_169_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_CollectLevelMVars_collect(v_u_164_, v___x_177_);
return v___x_178_;
}
}
}
else
{
lean_dec(v_u_164_);
return v_s_165_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_a_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_185_, v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_188_, lean_object* v_m_189_, lean_object* v_a_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(v_00_u03b2_188_, v_m_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_m_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_194_, v_a_195_, v_b_196_);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_202_, lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_202_, v_a_203_, v_x_204_);
lean_dec(v_x_204_);
lean_dec(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_207_, lean_object* v_data_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_data_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_210_, lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_211_, v_source_212_, v_target_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_key_221_; lean_object* v_value_222_; lean_object* v_tail_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v_key_221_ = lean_ctor_get(v_x_220_, 0);
v_value_222_ = lean_ctor_get(v_x_220_, 1);
v_tail_223_ = lean_ctor_get(v_x_220_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_246_ == 0)
{
v___x_225_ = v_x_220_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_tail_223_);
lean_inc(v_value_222_);
lean_inc(v_key_221_);
lean_dec(v_x_220_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_227_ = lean_array_get_size(v_x_219_);
v___x_228_ = l_Lean_Expr_hash(v_key_221_);
v___x_229_ = 32ULL;
v___x_230_ = lean_uint64_shift_right(v___x_228_, v___x_229_);
v_fold_231_ = lean_uint64_xor(v___x_228_, v___x_230_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_227_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v___x_240_ = lean_array_uget_borrowed(v_x_219_, v___x_239_);
lean_inc(v___x_240_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 2, v___x_240_);
v___x_242_ = v___x_225_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_key_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_value_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___x_240_);
v___x_242_ = v_reuseFailAlloc_245_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_array_uset(v_x_219_, v___x_239_, v___x_242_);
v_x_219_ = v___x_243_;
v_x_220_ = v_tail_223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(lean_object* v_i_247_, lean_object* v_source_248_, lean_object* v_target_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_get_size(v_source_248_);
v___x_251_ = lean_nat_dec_lt(v_i_247_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec_ref(v_source_248_);
lean_dec(v_i_247_);
return v_target_249_;
}
else
{
lean_object* v_es_252_; lean_object* v___x_253_; lean_object* v_source_254_; lean_object* v_target_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_es_252_ = lean_array_fget(v_source_248_, v_i_247_);
v___x_253_ = lean_box(0);
v_source_254_ = lean_array_fset(v_source_248_, v_i_247_, v___x_253_);
v_target_255_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_target_249_, v_es_252_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_i_247_, v___x_256_);
lean_dec(v_i_247_);
v_i_247_ = v___x_257_;
v_source_248_ = v_source_254_;
v_target_249_ = v_target_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object* v_data_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_nbuckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_array_get_size(v_data_259_);
v___x_261_ = lean_unsigned_to_nat(2u);
v_nbuckets_262_ = lean_nat_mul(v___x_260_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = lean_mk_array(v_nbuckets_262_, v___x_264_);
v___x_266_ = lean_array_propagate_mark(v_data_259_, v___x_265_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v___x_263_, v_data_259_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_tail_272_; uint8_t v___x_273_; 
v_key_271_ = lean_ctor_get(v_x_269_, 0);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v___x_273_ = lean_expr_eqv(v_key_271_, v_a_268_);
if (v___x_273_ == 0)
{
v_x_269_ = v_tail_272_;
goto _start;
}
else
{
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_275_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_a_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object* v_m_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_size_282_; lean_object* v_buckets_283_; lean_object* v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v_fold_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v_bkt_297_; uint8_t v___x_298_; 
v_size_282_ = lean_ctor_get(v_m_279_, 0);
v_buckets_283_ = lean_ctor_get(v_m_279_, 1);
v___x_284_ = lean_array_get_size(v_buckets_283_);
v___x_285_ = l_Lean_Expr_hash(v_a_280_);
v___x_286_ = 32ULL;
v___x_287_ = lean_uint64_shift_right(v___x_285_, v___x_286_);
v_fold_288_ = lean_uint64_xor(v___x_285_, v___x_287_);
v___x_289_ = 16ULL;
v___x_290_ = lean_uint64_shift_right(v_fold_288_, v___x_289_);
v___x_291_ = lean_uint64_xor(v_fold_288_, v___x_290_);
v___x_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = lean_usize_of_nat(v___x_284_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_sub(v___x_293_, v___x_294_);
v___x_296_ = lean_usize_land(v___x_292_, v___x_295_);
v_bkt_297_ = lean_array_uget_borrowed(v_buckets_283_, v___x_296_);
v___x_298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_280_, v_bkt_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_319_; 
lean_inc_ref(v_buckets_283_);
lean_inc(v_size_282_);
v_isSharedCheck_319_ = !lean_is_exclusive(v_m_279_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v_m_279_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_m_279_, 0);
lean_dec(v_unused_321_);
v___x_300_ = v_m_279_;
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
else
{
lean_dec(v_m_279_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_size_x27_303_; lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v_size_x27_303_ = lean_nat_add(v_size_282_, v___x_302_);
lean_dec(v_size_282_);
lean_inc(v_bkt_297_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v_a_280_);
lean_ctor_set(v___x_304_, 1, v_b_281_);
lean_ctor_set(v___x_304_, 2, v_bkt_297_);
v_buckets_x27_305_ = lean_array_uset(v_buckets_283_, v___x_296_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_mul(v_size_x27_303_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_div(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_array_get_size(v_buckets_x27_305_);
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v_val_312_; lean_object* v___x_314_; 
v_val_312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_buckets_x27_305_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_val_312_);
lean_ctor_set(v___x_300_, 0, v_size_x27_303_);
v___x_314_ = v___x_300_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_val_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v___x_317_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_buckets_x27_305_);
lean_ctor_set(v___x_300_, 0, v_size_x27_303_);
v___x_317_ = v___x_300_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_buckets_x27_305_);
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
else
{
lean_dec(v_b_281_);
lean_dec_ref(v_a_280_);
return v_m_279_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object* v_m_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_buckets_324_; lean_object* v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v_fold_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_buckets_324_ = lean_ctor_get(v_m_322_, 1);
v___x_325_ = lean_array_get_size(v_buckets_324_);
v___x_326_ = l_Lean_Expr_hash(v_a_323_);
v___x_327_ = 32ULL;
v___x_328_ = lean_uint64_shift_right(v___x_326_, v___x_327_);
v_fold_329_ = lean_uint64_xor(v___x_326_, v___x_328_);
v___x_330_ = 16ULL;
v___x_331_ = lean_uint64_shift_right(v_fold_329_, v___x_330_);
v___x_332_ = lean_uint64_xor(v_fold_329_, v___x_331_);
v___x_333_ = lean_uint64_to_usize(v___x_332_);
v___x_334_ = lean_usize_of_nat(v___x_325_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_sub(v___x_334_, v___x_335_);
v___x_337_ = lean_usize_land(v___x_333_, v___x_336_);
v___x_338_ = lean_array_uget_borrowed(v_buckets_324_, v___x_337_);
v___x_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_323_, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_340_, v_a_341_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_m_340_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
return v_x_344_;
}
else
{
lean_object* v_head_346_; lean_object* v_tail_347_; lean_object* v___x_348_; 
v_head_346_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_head_346_);
v_tail_347_ = lean_ctor_get(v_x_345_, 1);
lean_inc(v_tail_347_);
lean_dec_ref_known(v_x_345_, 2);
v___x_348_ = l_Lean_CollectLevelMVars_visitLevel(v_head_346_, v_x_344_);
v_x_344_ = v___x_348_;
v_x_345_ = v_tail_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* v_x_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_d_353_; lean_object* v_b_354_; lean_object* v___y_355_; 
switch(lean_obj_tag(v_x_350_))
{
case 11:
{
lean_object* v_struct_358_; lean_object* v___x_359_; 
v_struct_358_ = lean_ctor_get(v_x_350_, 2);
lean_inc_ref(v_struct_358_);
lean_dec_ref_known(v_x_350_, 3);
v___x_359_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_358_, v_a_351_);
return v___x_359_;
}
case 7:
{
lean_object* v_binderType_360_; lean_object* v_body_361_; 
v_binderType_360_ = lean_ctor_get(v_x_350_, 1);
lean_inc_ref(v_binderType_360_);
v_body_361_ = lean_ctor_get(v_x_350_, 2);
lean_inc_ref(v_body_361_);
lean_dec_ref_known(v_x_350_, 3);
v_d_353_ = v_binderType_360_;
v_b_354_ = v_body_361_;
v___y_355_ = v_a_351_;
goto v___jp_352_;
}
case 6:
{
lean_object* v_binderType_362_; lean_object* v_body_363_; 
v_binderType_362_ = lean_ctor_get(v_x_350_, 1);
lean_inc_ref(v_binderType_362_);
v_body_363_ = lean_ctor_get(v_x_350_, 2);
lean_inc_ref(v_body_363_);
lean_dec_ref_known(v_x_350_, 3);
v_d_353_ = v_binderType_362_;
v_b_354_ = v_body_363_;
v___y_355_ = v_a_351_;
goto v___jp_352_;
}
case 8:
{
lean_object* v_type_364_; lean_object* v_value_365_; lean_object* v_body_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_type_364_ = lean_ctor_get(v_x_350_, 1);
lean_inc_ref(v_type_364_);
v_value_365_ = lean_ctor_get(v_x_350_, 2);
lean_inc_ref(v_value_365_);
v_body_366_ = lean_ctor_get(v_x_350_, 3);
lean_inc_ref(v_body_366_);
lean_dec_ref_known(v_x_350_, 4);
v___x_367_ = l_Lean_CollectLevelMVars_visitExpr(v_type_364_, v_a_351_);
v___x_368_ = l_Lean_CollectLevelMVars_visitExpr(v_value_365_, v___x_367_);
v___x_369_ = l_Lean_CollectLevelMVars_visitExpr(v_body_366_, v___x_368_);
return v___x_369_;
}
case 5:
{
lean_object* v_fn_370_; lean_object* v_arg_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_fn_370_ = lean_ctor_get(v_x_350_, 0);
lean_inc_ref(v_fn_370_);
v_arg_371_ = lean_ctor_get(v_x_350_, 1);
lean_inc_ref(v_arg_371_);
lean_dec_ref_known(v_x_350_, 2);
v___x_372_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_370_, v_a_351_);
v___x_373_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_371_, v___x_372_);
return v___x_373_;
}
case 10:
{
lean_object* v_expr_374_; lean_object* v___x_375_; 
v_expr_374_ = lean_ctor_get(v_x_350_, 1);
lean_inc_ref(v_expr_374_);
lean_dec_ref_known(v_x_350_, 2);
v___x_375_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_374_, v_a_351_);
return v___x_375_;
}
case 4:
{
lean_object* v_us_376_; lean_object* v___x_377_; 
v_us_376_ = lean_ctor_get(v_x_350_, 1);
lean_inc(v_us_376_);
lean_dec_ref_known(v_x_350_, 2);
v___x_377_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(v_a_351_, v_us_376_);
return v___x_377_;
}
case 3:
{
lean_object* v_u_378_; lean_object* v___x_379_; 
v_u_378_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_u_378_);
lean_dec_ref_known(v_x_350_, 1);
v___x_379_ = l_Lean_CollectLevelMVars_visitLevel(v_u_378_, v_a_351_);
return v___x_379_;
}
default: 
{
lean_dec_ref(v_x_350_);
return v_a_351_;
}
}
v___jp_352_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Lean_CollectLevelMVars_visitExpr(v_d_353_, v___y_355_);
v___x_357_ = l_Lean_CollectLevelMVars_visitExpr(v_b_354_, v___x_356_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* v_e_380_, lean_object* v_s_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Expr_hasMVar(v_e_380_);
if (v___x_382_ == 0)
{
lean_dec_ref(v_e_380_);
return v_s_381_;
}
else
{
lean_object* v_visitedLevel_383_; lean_object* v_visitedExpr_384_; lean_object* v_result_385_; uint8_t v___x_386_; 
v_visitedLevel_383_ = lean_ctor_get(v_s_381_, 0);
v_visitedExpr_384_ = lean_ctor_get(v_s_381_, 1);
v_result_385_ = lean_ctor_get(v_s_381_, 2);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_384_, v_e_380_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
lean_inc_ref(v_result_385_);
lean_inc_ref(v_visitedExpr_384_);
lean_inc_ref(v_visitedLevel_383_);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_381_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_397_ = lean_ctor_get(v_s_381_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_s_381_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_s_381_, 0);
lean_dec(v_unused_399_);
v___x_388_ = v_s_381_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_s_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_box(0);
lean_inc_ref(v_e_380_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_384_, v_e_380_, v___x_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_visitedLevel_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_result_385_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_CollectLevelMVars_main(v_e_380_, v___x_393_);
return v___x_394_;
}
}
}
else
{
lean_dec_ref(v_e_380_);
return v_s_381_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_a_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_401_, v_a_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_404_, lean_object* v_m_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(v_00_u03b2_404_, v_m_405_, v_a_406_);
lean_dec_ref(v_a_406_);
lean_dec_ref(v_m_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_410_, v_a_411_, v_b_412_);
return v___x_413_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_a_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(v_00_u03b2_418_, v_a_419_, v_x_420_);
lean_dec(v_x_420_);
lean_dec_ref(v_a_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object* v_00_u03b2_423_, lean_object* v_data_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_data_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_426_, lean_object* v_i_427_, lean_object* v_source_428_, lean_object* v_target_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v_i_427_, v_source_428_, v_target_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_x_432_, v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object* v_s_435_, lean_object* v_e_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_CollectLevelMVars_main(v_e_436_, v_s_435_);
return v___x_437_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
