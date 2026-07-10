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
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_13_, lean_object* v_x_14_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3___redArg(lean_object* v_i_41_, lean_object* v_source_42_, lean_object* v_target_43_){
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
v_target_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(v_target_43_, v_es_46_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2___redArg(lean_object* v_data_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_nbuckets_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_54_ = lean_array_get_size(v_data_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v_nbuckets_56_ = lean_nat_mul(v___x_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_box(0);
v___x_59_ = lean_mk_array(v_nbuckets_56_, v___x_58_);
v___x_60_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3___redArg(v___x_57_, v_data_53_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_61_, lean_object* v_x_62_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_a_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object* v_m_72_, lean_object* v_a_73_, lean_object* v_b_74_){
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
v___x_91_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_73_, v_bkt_90_);
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
v_val_105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2___redArg(v_buckets_x27_98_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object* v_m_115_, lean_object* v_a_116_){
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
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_116_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg___boxed(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_m_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* v_u_137_, lean_object* v_s_138_){
_start:
{
uint8_t v___y_140_; uint8_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = l_Lean_Level_hasMVar(v_u_137_);
v___x_155_ = lean_bool_not(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v_visitedLevel_156_; uint8_t v___x_157_; 
v_visitedLevel_156_ = lean_ctor_get(v_s_138_, 0);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_156_, v_u_137_);
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
lean_object* v_visitedLevel_141_; lean_object* v_visitedExpr_142_; lean_object* v_result_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_visitedLevel_141_ = lean_ctor_get(v_s_138_, 0);
v_visitedExpr_142_ = lean_ctor_get(v_s_138_, 1);
v_result_143_ = lean_ctor_get(v_s_138_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_s_138_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v_s_138_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_result_143_);
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
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_141_, v_u_137_, v___x_147_);
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
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_result_143_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_CollectLevelMVars_collect(v_u_137_, v___x_150_);
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
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* v_x_158_, lean_object* v_a_159_){
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
v___x_167_ = l_Lean_CollectLevelMVars_visitLevel(v_a_166_, v_a_159_);
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
case 5:
{
lean_object* v_a_172_; lean_object* v_visitedLevel_173_; lean_object* v_visitedExpr_174_; lean_object* v_result_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_172_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v_x_158_, 1);
v_visitedLevel_173_ = lean_ctor_get(v_a_159_, 0);
v_visitedExpr_174_ = lean_ctor_get(v_a_159_, 1);
v_result_175_ = lean_ctor_get(v_a_159_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_a_159_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_result_175_);
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
v___x_179_ = lean_array_push(v_result_175_, v_a_172_);
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
v___x_164_ = l_Lean_CollectLevelMVars_visitLevel(v_u_161_, v___y_163_);
v___x_165_ = l_Lean_CollectLevelMVars_visitLevel(v_v_162_, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_185_, v_a_186_, v_b_187_);
return v___x_188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object* v_00_u03b2_189_, lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_190_, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1___boxed(lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__1(v_00_u03b2_193_, v_m_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_m_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_202_, lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_202_, v_a_203_, v_x_204_);
lean_dec(v_x_204_);
lean_dec(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2(lean_object* v_00_u03b2_207_, lean_object* v_data_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2___redArg(v_data_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_210_, lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3___redArg(v_i_211_, v_source_212_, v_target_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__2_spec__3_spec__5___redArg(v_x_216_, v_x_217_);
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
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_nbuckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_260_ = lean_array_get_size(v_data_259_);
v___x_261_ = lean_unsigned_to_nat(2u);
v_nbuckets_262_ = lean_nat_mul(v___x_260_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = lean_mk_array(v_nbuckets_262_, v___x_264_);
v___x_266_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v___x_263_, v_data_259_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
uint8_t v___x_269_; 
v___x_269_ = 0;
return v___x_269_;
}
else
{
lean_object* v_key_270_; lean_object* v_tail_271_; uint8_t v___x_272_; 
v_key_270_ = lean_ctor_get(v_x_268_, 0);
v_tail_271_ = lean_ctor_get(v_x_268_, 2);
v___x_272_ = lean_expr_eqv(v_key_270_, v_a_267_);
if (v___x_272_ == 0)
{
v_x_268_ = v_tail_271_;
goto _start;
}
else
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_274_, lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_274_, v_x_275_);
lean_dec(v_x_275_);
lean_dec_ref(v_a_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object* v_m_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_size_281_; lean_object* v_buckets_282_; lean_object* v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v_fold_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v_bkt_296_; uint8_t v___x_297_; 
v_size_281_ = lean_ctor_get(v_m_278_, 0);
v_buckets_282_ = lean_ctor_get(v_m_278_, 1);
v___x_283_ = lean_array_get_size(v_buckets_282_);
v___x_284_ = l_Lean_Expr_hash(v_a_279_);
v___x_285_ = 32ULL;
v___x_286_ = lean_uint64_shift_right(v___x_284_, v___x_285_);
v_fold_287_ = lean_uint64_xor(v___x_284_, v___x_286_);
v___x_288_ = 16ULL;
v___x_289_ = lean_uint64_shift_right(v_fold_287_, v___x_288_);
v___x_290_ = lean_uint64_xor(v_fold_287_, v___x_289_);
v___x_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = lean_usize_of_nat(v___x_283_);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_sub(v___x_292_, v___x_293_);
v___x_295_ = lean_usize_land(v___x_291_, v___x_294_);
v_bkt_296_ = lean_array_uget_borrowed(v_buckets_282_, v___x_295_);
v___x_297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_279_, v_bkt_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_318_; 
lean_inc_ref(v_buckets_282_);
lean_inc(v_size_281_);
v_isSharedCheck_318_ = !lean_is_exclusive(v_m_278_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; 
v_unused_319_ = lean_ctor_get(v_m_278_, 1);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_m_278_, 0);
lean_dec(v_unused_320_);
v___x_299_ = v_m_278_;
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
else
{
lean_dec(v_m_278_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v_size_x27_302_; lean_object* v___x_303_; lean_object* v_buckets_x27_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v_size_x27_302_ = lean_nat_add(v_size_281_, v___x_301_);
lean_dec(v_size_281_);
lean_inc(v_bkt_296_);
v___x_303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_303_, 0, v_a_279_);
lean_ctor_set(v___x_303_, 1, v_b_280_);
lean_ctor_set(v___x_303_, 2, v_bkt_296_);
v_buckets_x27_304_ = lean_array_uset(v_buckets_282_, v___x_295_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(4u);
v___x_306_ = lean_nat_mul(v_size_x27_302_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(3u);
v___x_308_ = lean_nat_div(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_array_get_size(v_buckets_x27_304_);
v___x_310_ = lean_nat_dec_le(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
if (v___x_310_ == 0)
{
lean_object* v_val_311_; lean_object* v___x_313_; 
v_val_311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_buckets_x27_304_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_val_311_);
lean_ctor_set(v___x_299_, 0, v_size_x27_302_);
v___x_313_ = v___x_299_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_size_x27_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_val_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
lean_object* v___x_316_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_buckets_x27_304_);
lean_ctor_set(v___x_299_, 0, v_size_x27_302_);
v___x_316_ = v___x_299_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_size_x27_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_buckets_x27_304_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_dec(v_b_280_);
lean_dec_ref(v_a_279_);
return v_m_278_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_buckets_323_; lean_object* v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v_fold_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_buckets_323_ = lean_ctor_get(v_m_321_, 1);
v___x_324_ = lean_array_get_size(v_buckets_323_);
v___x_325_ = l_Lean_Expr_hash(v_a_322_);
v___x_326_ = 32ULL;
v___x_327_ = lean_uint64_shift_right(v___x_325_, v___x_326_);
v_fold_328_ = lean_uint64_xor(v___x_325_, v___x_327_);
v___x_329_ = 16ULL;
v___x_330_ = lean_uint64_shift_right(v_fold_328_, v___x_329_);
v___x_331_ = lean_uint64_xor(v_fold_328_, v___x_330_);
v___x_332_ = lean_uint64_to_usize(v___x_331_);
v___x_333_ = lean_usize_of_nat(v___x_324_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_sub(v___x_333_, v___x_334_);
v___x_336_ = lean_usize_land(v___x_332_, v___x_335_);
v___x_337_ = lean_array_uget_borrowed(v_buckets_323_, v___x_336_);
v___x_338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_322_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_339_, v_a_340_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_m_339_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
return v_x_343_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v___x_347_; 
v_head_345_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_head_345_);
v_tail_346_ = lean_ctor_get(v_x_344_, 1);
lean_inc(v_tail_346_);
lean_dec_ref_known(v_x_344_, 2);
v___x_347_ = l_Lean_CollectLevelMVars_visitLevel(v_head_345_, v_x_343_);
v_x_343_ = v___x_347_;
v_x_344_ = v_tail_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* v_x_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_d_352_; lean_object* v_b_353_; lean_object* v___y_354_; 
switch(lean_obj_tag(v_x_349_))
{
case 11:
{
lean_object* v_struct_357_; lean_object* v___x_358_; 
v_struct_357_ = lean_ctor_get(v_x_349_, 2);
lean_inc_ref(v_struct_357_);
lean_dec_ref_known(v_x_349_, 3);
v___x_358_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_357_, v_a_350_);
return v___x_358_;
}
case 7:
{
lean_object* v_binderType_359_; lean_object* v_body_360_; 
v_binderType_359_ = lean_ctor_get(v_x_349_, 1);
lean_inc_ref(v_binderType_359_);
v_body_360_ = lean_ctor_get(v_x_349_, 2);
lean_inc_ref(v_body_360_);
lean_dec_ref_known(v_x_349_, 3);
v_d_352_ = v_binderType_359_;
v_b_353_ = v_body_360_;
v___y_354_ = v_a_350_;
goto v___jp_351_;
}
case 6:
{
lean_object* v_binderType_361_; lean_object* v_body_362_; 
v_binderType_361_ = lean_ctor_get(v_x_349_, 1);
lean_inc_ref(v_binderType_361_);
v_body_362_ = lean_ctor_get(v_x_349_, 2);
lean_inc_ref(v_body_362_);
lean_dec_ref_known(v_x_349_, 3);
v_d_352_ = v_binderType_361_;
v_b_353_ = v_body_362_;
v___y_354_ = v_a_350_;
goto v___jp_351_;
}
case 8:
{
lean_object* v_type_363_; lean_object* v_value_364_; lean_object* v_body_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_type_363_ = lean_ctor_get(v_x_349_, 1);
lean_inc_ref(v_type_363_);
v_value_364_ = lean_ctor_get(v_x_349_, 2);
lean_inc_ref(v_value_364_);
v_body_365_ = lean_ctor_get(v_x_349_, 3);
lean_inc_ref(v_body_365_);
lean_dec_ref_known(v_x_349_, 4);
v___x_366_ = l_Lean_CollectLevelMVars_visitExpr(v_type_363_, v_a_350_);
v___x_367_ = l_Lean_CollectLevelMVars_visitExpr(v_value_364_, v___x_366_);
v___x_368_ = l_Lean_CollectLevelMVars_visitExpr(v_body_365_, v___x_367_);
return v___x_368_;
}
case 5:
{
lean_object* v_fn_369_; lean_object* v_arg_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_fn_369_ = lean_ctor_get(v_x_349_, 0);
lean_inc_ref(v_fn_369_);
v_arg_370_ = lean_ctor_get(v_x_349_, 1);
lean_inc_ref(v_arg_370_);
lean_dec_ref_known(v_x_349_, 2);
v___x_371_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_369_, v_a_350_);
v___x_372_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_370_, v___x_371_);
return v___x_372_;
}
case 10:
{
lean_object* v_expr_373_; lean_object* v___x_374_; 
v_expr_373_ = lean_ctor_get(v_x_349_, 1);
lean_inc_ref(v_expr_373_);
lean_dec_ref_known(v_x_349_, 2);
v___x_374_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_373_, v_a_350_);
return v___x_374_;
}
case 4:
{
lean_object* v_us_375_; lean_object* v___x_376_; 
v_us_375_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_us_375_);
lean_dec_ref_known(v_x_349_, 2);
v___x_376_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(v_a_350_, v_us_375_);
return v___x_376_;
}
case 3:
{
lean_object* v_u_377_; lean_object* v___x_378_; 
v_u_377_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_u_377_);
lean_dec_ref_known(v_x_349_, 1);
v___x_378_ = l_Lean_CollectLevelMVars_visitLevel(v_u_377_, v_a_350_);
return v___x_378_;
}
default: 
{
lean_dec_ref(v_x_349_);
return v_a_350_;
}
}
v___jp_351_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Lean_CollectLevelMVars_visitExpr(v_d_352_, v___y_354_);
v___x_356_ = l_Lean_CollectLevelMVars_visitExpr(v_b_353_, v___x_355_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* v_e_379_, lean_object* v_s_380_){
_start:
{
uint8_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = l_Lean_Expr_hasMVar(v_e_379_);
v___x_382_ = lean_bool_not(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v_visitedLevel_383_; lean_object* v_visitedExpr_384_; lean_object* v_result_385_; uint8_t v___x_386_; 
v_visitedLevel_383_ = lean_ctor_get(v_s_380_, 0);
v_visitedExpr_384_ = lean_ctor_get(v_s_380_, 1);
v_result_385_ = lean_ctor_get(v_s_380_, 2);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_384_, v_e_379_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
lean_inc_ref(v_result_385_);
lean_inc_ref(v_visitedExpr_384_);
lean_inc_ref(v_visitedLevel_383_);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_380_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_397_ = lean_ctor_get(v_s_380_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_s_380_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_s_380_, 0);
lean_dec(v_unused_399_);
v___x_388_ = v_s_380_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_s_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_box(0);
lean_inc_ref(v_e_379_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_384_, v_e_379_, v___x_390_);
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
v___x_394_ = l_Lean_CollectLevelMVars_main(v_e_379_, v___x_393_);
return v___x_394_;
}
}
}
else
{
lean_dec_ref(v_e_379_);
return v_s_380_;
}
}
else
{
lean_dec_ref(v_e_379_);
return v_s_380_;
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
