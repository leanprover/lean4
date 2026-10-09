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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_13_ = stack[0].m_obj;
lean_object* v_x_14_ = stack[1].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_13_, v_x_14_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_a_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_a_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object* v_m_25_, lean_object* v_a_26_){
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
v___x_42_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_26_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_25_ = stack[0].m_obj;
lean_object* v_a_26_ = stack[1].m_obj;
uint8_t v_res_43_;
v_res_43_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_25_, v_a_26_);
stack->m_num = v_res_43_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(lean_object* v_m_44_, lean_object* v_a_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_m_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_48_, lean_object* v_x_49_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(lean_object* v_i_76_, lean_object* v_source_77_, lean_object* v_target_78_){
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
v_target_84_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_78_, v_es_81_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(lean_object* v_data_88_){
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
v___x_96_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_92_, v_data_88_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
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
v___x_116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_98_, v_bkt_115_);
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
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_123_);
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
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* v_x_140_, lean_object* v_a_141_){
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
v___x_149_ = l_Lean_CollectLevelMVars_visitLevel(v_a_148_, v_a_141_);
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
case 5:
{
lean_object* v_a_154_; lean_object* v_visitedLevel_155_; lean_object* v_visitedExpr_156_; lean_object* v_result_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_a_154_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v_x_140_, 1);
v_visitedLevel_155_ = lean_ctor_get(v_a_141_, 0);
v_visitedExpr_156_ = lean_ctor_get(v_a_141_, 1);
v_result_157_ = lean_ctor_get(v_a_141_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v_a_141_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_result_157_);
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
v___x_161_ = lean_array_push(v_result_157_, v_a_154_);
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
v___x_146_ = l_Lean_CollectLevelMVars_visitLevel(v_u_143_, v___y_145_);
v___x_147_ = l_Lean_CollectLevelMVars_visitLevel(v_v_144_, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* v_u_166_, lean_object* v_s_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Level_hasMVar(v_u_166_);
if (v___x_168_ == 0)
{
lean_dec(v_u_166_);
return v_s_167_;
}
else
{
lean_object* v_visitedLevel_169_; lean_object* v_visitedExpr_170_; lean_object* v_result_171_; uint8_t v___x_172_; 
v_visitedLevel_169_ = lean_ctor_get(v_s_167_, 0);
v_visitedExpr_170_ = lean_ctor_get(v_s_167_, 1);
v_result_171_ = lean_ctor_get(v_s_167_, 2);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_169_, v_u_166_);
if (v___x_172_ == 0)
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_result_171_);
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
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_169_, v_u_166_, v___x_176_);
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
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_result_171_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_CollectLevelMVars_collect(v_u_166_, v___x_179_);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_187_, v_a_188_);
return v___x_189_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
uint8_t v_res_190_;
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_box(0), v_m_187_, v_a_188_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_191_, lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(v_00_u03b2_191_, v_m_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_m_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object* v_00_u03b2_196_, lean_object* v_m_197_, lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_197_, v_a_198_, v_b_199_);
return v___x_200_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[1].m_obj;
lean_object* v_x_203_ = stack[2].m_obj;
uint8_t v_res_205_;
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_box(0), v_a_202_, v_x_203_);
stack->m_num = v_res_205_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_206_, lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_206_, v_a_207_, v_x_208_);
lean_dec(v_x_208_);
lean_dec(v_a_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_211_, lean_object* v_data_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_data_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_214_, lean_object* v_i_215_, lean_object* v_source_216_, lean_object* v_target_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_215_, v_source_216_, v_target_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
return v_x_223_;
}
else
{
lean_object* v_key_225_; lean_object* v_value_226_; lean_object* v_tail_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_250_; 
v_key_225_ = lean_ctor_get(v_x_224_, 0);
v_value_226_ = lean_ctor_get(v_x_224_, 1);
v_tail_227_ = lean_ctor_get(v_x_224_, 2);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_250_ == 0)
{
v___x_229_ = v_x_224_;
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_tail_227_);
lean_inc(v_value_226_);
lean_inc(v_key_225_);
lean_dec(v_x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_231_ = lean_array_get_size(v_x_223_);
v___x_232_ = l_Lean_Expr_hash(v_key_225_);
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___x_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_231_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_array_uget_borrowed(v_x_223_, v___x_243_);
lean_inc(v___x_244_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 2, v___x_244_);
v___x_246_ = v___x_229_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_key_225_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_value_226_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___x_244_);
v___x_246_ = v_reuseFailAlloc_249_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_array_uset(v_x_223_, v___x_243_, v___x_246_);
v_x_223_ = v___x_247_;
v_x_224_ = v_tail_227_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(lean_object* v_i_251_, lean_object* v_source_252_, lean_object* v_target_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_array_get_size(v_source_252_);
v___x_255_ = lean_nat_dec_lt(v_i_251_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec_ref(v_source_252_);
lean_dec(v_i_251_);
return v_target_253_;
}
else
{
lean_object* v_es_256_; lean_object* v___x_257_; lean_object* v_source_258_; lean_object* v_target_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_es_256_ = lean_array_fget(v_source_252_, v_i_251_);
v___x_257_ = lean_box(0);
v_source_258_ = lean_array_fset(v_source_252_, v_i_251_, v___x_257_);
v_target_259_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_target_253_, v_es_256_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_i_251_, v___x_260_);
lean_dec(v_i_251_);
v_i_251_ = v___x_261_;
v_source_252_ = v_source_258_;
v_target_253_ = v_target_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object* v_data_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_nbuckets_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_264_ = lean_array_get_size(v_data_263_);
v___x_265_ = lean_unsigned_to_nat(2u);
v_nbuckets_266_ = lean_nat_mul(v___x_264_, v___x_265_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_box(0);
v___x_269_ = lean_mk_array(v_nbuckets_266_, v___x_268_);
v___x_270_ = lean_array_propagate_mark(v_data_263_, v___x_269_);
v___x_271_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v___x_267_, v_data_263_, v___x_270_);
return v___x_271_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object* v_a_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
else
{
lean_object* v_key_275_; lean_object* v_tail_276_; uint8_t v___x_277_; 
v_key_275_ = lean_ctor_get(v_x_273_, 0);
v_tail_276_ = lean_ctor_get(v_x_273_, 2);
v___x_277_ = lean_expr_eqv(v_key_275_, v_a_272_);
if (v___x_277_ == 0)
{
v_x_273_ = v_tail_276_;
goto _start;
}
else
{
return v___x_277_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_272_ = stack[0].m_obj;
lean_object* v_x_273_ = stack[1].m_obj;
uint8_t v_res_279_;
v_res_279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_272_, v_x_273_);
stack->m_num = v_res_279_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_280_, v_x_281_);
lean_dec(v_x_281_);
lean_dec_ref(v_a_280_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object* v_m_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_size_287_; lean_object* v_buckets_288_; lean_object* v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v_bkt_302_; uint8_t v___x_303_; 
v_size_287_ = lean_ctor_get(v_m_284_, 0);
v_buckets_288_ = lean_ctor_get(v_m_284_, 1);
v___x_289_ = lean_array_get_size(v_buckets_288_);
v___x_290_ = l_Lean_Expr_hash(v_a_285_);
v___x_291_ = 32ULL;
v___x_292_ = lean_uint64_shift_right(v___x_290_, v___x_291_);
v_fold_293_ = lean_uint64_xor(v___x_290_, v___x_292_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_289_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v_bkt_302_ = lean_array_uget_borrowed(v_buckets_288_, v___x_301_);
v___x_303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_285_, v_bkt_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_324_; 
lean_inc_ref(v_buckets_288_);
lean_inc(v_size_287_);
v_isSharedCheck_324_ = !lean_is_exclusive(v_m_284_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_325_ = lean_ctor_get(v_m_284_, 1);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_m_284_, 0);
lean_dec(v_unused_326_);
v___x_305_ = v_m_284_;
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_m_284_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v_size_x27_308_; lean_object* v___x_309_; lean_object* v_buckets_x27_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v_size_x27_308_ = lean_nat_add(v_size_287_, v___x_307_);
lean_dec(v_size_287_);
lean_inc(v_bkt_302_);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v_a_285_);
lean_ctor_set(v___x_309_, 1, v_b_286_);
lean_ctor_set(v___x_309_, 2, v_bkt_302_);
v_buckets_x27_310_ = lean_array_uset(v_buckets_288_, v___x_301_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(4u);
v___x_312_ = lean_nat_mul(v_size_x27_308_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(3u);
v___x_314_ = lean_nat_div(v___x_312_, v___x_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_array_get_size(v_buckets_x27_310_);
v___x_316_ = lean_nat_dec_le(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
if (v___x_316_ == 0)
{
lean_object* v_val_317_; lean_object* v___x_319_; 
v_val_317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_buckets_x27_310_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_val_317_);
lean_ctor_set(v___x_305_, 0, v_size_x27_308_);
v___x_319_ = v___x_305_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_size_x27_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_val_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v___x_322_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_buckets_x27_310_);
lean_ctor_set(v___x_305_, 0, v_size_x27_308_);
v___x_322_ = v___x_305_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_size_x27_308_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_buckets_x27_310_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_dec(v_b_286_);
lean_dec_ref(v_a_285_);
return v_m_284_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_buckets_329_; lean_object* v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v_fold_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_buckets_329_ = lean_ctor_get(v_m_327_, 1);
v___x_330_ = lean_array_get_size(v_buckets_329_);
v___x_331_ = l_Lean_Expr_hash(v_a_328_);
v___x_332_ = 32ULL;
v___x_333_ = lean_uint64_shift_right(v___x_331_, v___x_332_);
v_fold_334_ = lean_uint64_xor(v___x_331_, v___x_333_);
v___x_335_ = 16ULL;
v___x_336_ = lean_uint64_shift_right(v_fold_334_, v___x_335_);
v___x_337_ = lean_uint64_xor(v_fold_334_, v___x_336_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = lean_usize_of_nat(v___x_330_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_sub(v___x_339_, v___x_340_);
v___x_342_ = lean_usize_land(v___x_338_, v___x_341_);
v___x_343_ = lean_array_uget_borrowed(v_buckets_329_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_328_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_327_ = stack[0].m_obj;
lean_object* v_a_328_ = stack[1].m_obj;
uint8_t v_res_345_;
v_res_345_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_327_, v_a_328_);
stack->m_num = v_res_345_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
return v_x_350_;
}
else
{
lean_object* v_head_352_; lean_object* v_tail_353_; lean_object* v___x_354_; 
v_head_352_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_head_352_);
v_tail_353_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_tail_353_);
lean_dec_ref_known(v_x_351_, 2);
v___x_354_ = l_Lean_CollectLevelMVars_visitLevel(v_head_352_, v_x_350_);
v_x_350_ = v___x_354_;
v_x_351_ = v_tail_353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* v_x_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_d_359_; lean_object* v_b_360_; lean_object* v___y_361_; 
switch(lean_obj_tag(v_x_356_))
{
case 11:
{
lean_object* v_struct_364_; lean_object* v___x_365_; 
v_struct_364_ = lean_ctor_get(v_x_356_, 2);
lean_inc_ref(v_struct_364_);
lean_dec_ref_known(v_x_356_, 3);
v___x_365_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_364_, v_a_357_);
return v___x_365_;
}
case 7:
{
lean_object* v_binderType_366_; lean_object* v_body_367_; 
v_binderType_366_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_binderType_366_);
v_body_367_ = lean_ctor_get(v_x_356_, 2);
lean_inc_ref(v_body_367_);
lean_dec_ref_known(v_x_356_, 3);
v_d_359_ = v_binderType_366_;
v_b_360_ = v_body_367_;
v___y_361_ = v_a_357_;
goto v___jp_358_;
}
case 6:
{
lean_object* v_binderType_368_; lean_object* v_body_369_; 
v_binderType_368_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_binderType_368_);
v_body_369_ = lean_ctor_get(v_x_356_, 2);
lean_inc_ref(v_body_369_);
lean_dec_ref_known(v_x_356_, 3);
v_d_359_ = v_binderType_368_;
v_b_360_ = v_body_369_;
v___y_361_ = v_a_357_;
goto v___jp_358_;
}
case 8:
{
lean_object* v_type_370_; lean_object* v_value_371_; lean_object* v_body_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_type_370_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_type_370_);
v_value_371_ = lean_ctor_get(v_x_356_, 2);
lean_inc_ref(v_value_371_);
v_body_372_ = lean_ctor_get(v_x_356_, 3);
lean_inc_ref(v_body_372_);
lean_dec_ref_known(v_x_356_, 4);
v___x_373_ = l_Lean_CollectLevelMVars_visitExpr(v_type_370_, v_a_357_);
v___x_374_ = l_Lean_CollectLevelMVars_visitExpr(v_value_371_, v___x_373_);
v___x_375_ = l_Lean_CollectLevelMVars_visitExpr(v_body_372_, v___x_374_);
return v___x_375_;
}
case 5:
{
lean_object* v_fn_376_; lean_object* v_arg_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_fn_376_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_fn_376_);
v_arg_377_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_arg_377_);
lean_dec_ref_known(v_x_356_, 2);
v___x_378_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_376_, v_a_357_);
v___x_379_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_377_, v___x_378_);
return v___x_379_;
}
case 10:
{
lean_object* v_expr_380_; lean_object* v___x_381_; 
v_expr_380_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_expr_380_);
lean_dec_ref_known(v_x_356_, 2);
v___x_381_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_380_, v_a_357_);
return v___x_381_;
}
case 4:
{
lean_object* v_us_382_; lean_object* v___x_383_; 
v_us_382_ = lean_ctor_get(v_x_356_, 1);
lean_inc(v_us_382_);
lean_dec_ref_known(v_x_356_, 2);
v___x_383_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(v_a_357_, v_us_382_);
return v___x_383_;
}
case 3:
{
lean_object* v_u_384_; lean_object* v___x_385_; 
v_u_384_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_u_384_);
lean_dec_ref_known(v_x_356_, 1);
v___x_385_ = l_Lean_CollectLevelMVars_visitLevel(v_u_384_, v_a_357_);
return v___x_385_;
}
default: 
{
lean_dec_ref(v_x_356_);
return v_a_357_;
}
}
v___jp_358_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_CollectLevelMVars_visitExpr(v_d_359_, v___y_361_);
v___x_363_ = l_Lean_CollectLevelMVars_visitExpr(v_b_360_, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* v_e_386_, lean_object* v_s_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Expr_hasMVar(v_e_386_);
if (v___x_388_ == 0)
{
lean_dec_ref(v_e_386_);
return v_s_387_;
}
else
{
lean_object* v_visitedLevel_389_; lean_object* v_visitedExpr_390_; lean_object* v_result_391_; uint8_t v___x_392_; 
v_visitedLevel_389_ = lean_ctor_get(v_s_387_, 0);
v_visitedExpr_390_ = lean_ctor_get(v_s_387_, 1);
v_result_391_ = lean_ctor_get(v_s_387_, 2);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_390_, v_e_386_);
if (v___x_392_ == 0)
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_402_; 
lean_inc_ref(v_result_391_);
lean_inc_ref(v_visitedExpr_390_);
lean_inc_ref(v_visitedLevel_389_);
v_isSharedCheck_402_ = !lean_is_exclusive(v_s_387_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; 
v_unused_403_ = lean_ctor_get(v_s_387_, 2);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_s_387_, 1);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_s_387_, 0);
lean_dec(v_unused_405_);
v___x_394_ = v_s_387_;
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_s_387_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
lean_inc_ref(v_e_386_);
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_390_, v_e_386_, v___x_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_visitedLevel_389_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_result_391_);
v___x_399_ = v_reuseFailAlloc_401_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_CollectLevelMVars_main(v_e_386_, v___x_399_);
return v___x_400_;
}
}
}
else
{
lean_dec_ref(v_e_386_);
return v_s_387_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_407_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_407_ = stack[1].m_obj;
lean_object* v_a_408_ = stack[2].m_obj;
uint8_t v_res_410_;
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_box(0), v_m_407_, v_a_408_);
stack->m_num = v_res_410_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(v_00_u03b2_411_, v_m_412_, v_a_413_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_m_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_417_, v_a_418_, v_b_419_);
return v___x_420_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object* v_00_u03b2_421_, lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_422_, v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_422_ = stack[1].m_obj;
lean_object* v_x_423_ = stack[2].m_obj;
uint8_t v_res_425_;
v_res_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_box(0), v_a_422_, v_x_423_);
stack->m_num = v_res_425_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(v_00_u03b2_426_, v_a_427_, v_x_428_);
lean_dec(v_x_428_);
lean_dec_ref(v_a_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object* v_00_u03b2_431_, lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_data_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_434_, lean_object* v_i_435_, lean_object* v_source_436_, lean_object* v_target_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v_i_435_, v_source_436_, v_target_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_x_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object* v_s_443_, lean_object* v_e_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_CollectLevelMVars_main(v_e_444_, v_s_443_);
return v___x_445_;
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
