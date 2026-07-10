// Lean compiler output
// Module: Lean.Util.CollectFVars
// Imports: public import Lean.LocalContext
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__1;
static const lean_array_object l_Lean_CollectFVars_instInhabitedState_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__2 = (const lean_object*)&l_Lean_CollectFVars_instInhabitedState_default___closed__2_value;
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__0, &l_Lean_CollectFVars_instInhabitedState_default___closed__0_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l_Lean_CollectFVars_instInhabitedState_default___closed__2));
v___x_10_ = lean_box(1);
v___x_11_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__1, &l_Lean_CollectFVars_instInhabitedState_default___closed__1_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__3, &l_Lean_CollectFVars_instInhabitedState_default___closed__3_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__3);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_CollectFVars_instInhabitedState_default;
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object* v_s_15_, lean_object* v_fvarId_16_){
_start:
{
lean_object* v_visitedExpr_17_; lean_object* v_fvarSet_18_; lean_object* v_fvarIds_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_28_; 
v_visitedExpr_17_ = lean_ctor_get(v_s_15_, 0);
v_fvarSet_18_ = lean_ctor_get(v_s_15_, 1);
v_fvarIds_19_ = lean_ctor_get(v_s_15_, 2);
v_isSharedCheck_28_ = !lean_is_exclusive(v_s_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_21_ = v_s_15_;
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_fvarIds_19_);
lean_inc(v_fvarSet_18_);
lean_inc(v_visitedExpr_17_);
lean_dec(v_s_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
lean_inc(v_fvarId_16_);
v___x_23_ = l_Lean_FVarIdSet_insert(v_fvarSet_18_, v_fvarId_16_);
v___x_24_ = lean_array_push(v_fvarIds_19_, v_fvarId_16_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_24_);
lean_ctor_set(v___x_21_, 1, v___x_23_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_visitedExpr_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
return v_x_29_;
}
else
{
lean_object* v_key_31_; lean_object* v_value_32_; lean_object* v_tail_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_56_; 
v_key_31_ = lean_ctor_get(v_x_30_, 0);
v_value_32_ = lean_ctor_get(v_x_30_, 1);
v_tail_33_ = lean_ctor_get(v_x_30_, 2);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_30_);
if (v_isSharedCheck_56_ == 0)
{
v___x_35_ = v_x_30_;
v_isShared_36_ = v_isSharedCheck_56_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_tail_33_);
lean_inc(v_value_32_);
lean_inc(v_key_31_);
lean_dec(v_x_30_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_56_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; uint64_t v_fold_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; size_t v___x_45_; size_t v___x_46_; size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_37_ = lean_array_get_size(v_x_29_);
v___x_38_ = l_Lean_Expr_hash(v_key_31_);
v___x_39_ = 32ULL;
v___x_40_ = lean_uint64_shift_right(v___x_38_, v___x_39_);
v_fold_41_ = lean_uint64_xor(v___x_38_, v___x_40_);
v___x_42_ = 16ULL;
v___x_43_ = lean_uint64_shift_right(v_fold_41_, v___x_42_);
v___x_44_ = lean_uint64_xor(v_fold_41_, v___x_43_);
v___x_45_ = lean_uint64_to_usize(v___x_44_);
v___x_46_ = lean_usize_of_nat(v___x_37_);
v___x_47_ = ((size_t)1ULL);
v___x_48_ = lean_usize_sub(v___x_46_, v___x_47_);
v___x_49_ = lean_usize_land(v___x_45_, v___x_48_);
v___x_50_ = lean_array_uget_borrowed(v_x_29_, v___x_49_);
lean_inc(v___x_50_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 2, v___x_50_);
v___x_52_ = v___x_35_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_key_31_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_value_32_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v___x_50_);
v___x_52_ = v_reuseFailAlloc_55_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; 
v___x_53_ = lean_array_uset(v_x_29_, v___x_49_, v___x_52_);
v_x_29_ = v___x_53_;
v_x_30_ = v_tail_33_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3___redArg(lean_object* v_i_57_, lean_object* v_source_58_, lean_object* v_target_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_source_58_);
v___x_61_ = lean_nat_dec_lt(v_i_57_, v___x_60_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_source_58_);
lean_dec(v_i_57_);
return v_target_59_;
}
else
{
lean_object* v_es_62_; lean_object* v___x_63_; lean_object* v_source_64_; lean_object* v_target_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_es_62_ = lean_array_fget(v_source_58_, v_i_57_);
v___x_63_ = lean_box(0);
v_source_64_ = lean_array_fset(v_source_58_, v_i_57_, v___x_63_);
v_target_65_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(v_target_59_, v_es_62_);
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_i_57_, v___x_66_);
lean_dec(v_i_57_);
v_i_57_ = v___x_67_;
v_source_58_ = v_source_64_;
v_target_59_ = v_target_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2___redArg(lean_object* v_data_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_nbuckets_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_array_get_size(v_data_69_);
v___x_71_ = lean_unsigned_to_nat(2u);
v_nbuckets_72_ = lean_nat_mul(v___x_70_, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_box(0);
v___x_75_ = lean_mk_array(v_nbuckets_72_, v___x_74_);
v___x_76_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3___redArg(v___x_73_, v_data_69_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
else
{
lean_object* v_key_80_; lean_object* v_tail_81_; uint8_t v___x_82_; 
v_key_80_ = lean_ctor_get(v_x_78_, 0);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v___x_82_ = lean_expr_eqv(v_key_80_, v_a_77_);
if (v___x_82_ == 0)
{
v_x_78_ = v_tail_81_;
goto _start;
}
else
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec_ref(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object* v_m_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
lean_object* v_size_91_; lean_object* v_buckets_92_; lean_object* v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v_fold_97_; uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; lean_object* v_bkt_106_; uint8_t v___x_107_; 
v_size_91_ = lean_ctor_get(v_m_88_, 0);
v_buckets_92_ = lean_ctor_get(v_m_88_, 1);
v___x_93_ = lean_array_get_size(v_buckets_92_);
v___x_94_ = l_Lean_Expr_hash(v_a_89_);
v___x_95_ = 32ULL;
v___x_96_ = lean_uint64_shift_right(v___x_94_, v___x_95_);
v_fold_97_ = lean_uint64_xor(v___x_94_, v___x_96_);
v___x_98_ = 16ULL;
v___x_99_ = lean_uint64_shift_right(v_fold_97_, v___x_98_);
v___x_100_ = lean_uint64_xor(v_fold_97_, v___x_99_);
v___x_101_ = lean_uint64_to_usize(v___x_100_);
v___x_102_ = lean_usize_of_nat(v___x_93_);
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_sub(v___x_102_, v___x_103_);
v___x_105_ = lean_usize_land(v___x_101_, v___x_104_);
v_bkt_106_ = lean_array_uget_borrowed(v_buckets_92_, v___x_105_);
v___x_107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_89_, v_bkt_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_128_; 
lean_inc_ref(v_buckets_92_);
lean_inc(v_size_91_);
v_isSharedCheck_128_ = !lean_is_exclusive(v_m_88_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_129_ = lean_ctor_get(v_m_88_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_m_88_, 0);
lean_dec(v_unused_130_);
v___x_109_ = v_m_88_;
v_isShared_110_ = v_isSharedCheck_128_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_m_88_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_128_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v_size_x27_112_; lean_object* v___x_113_; lean_object* v_buckets_x27_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v_size_x27_112_ = lean_nat_add(v_size_91_, v___x_111_);
lean_dec(v_size_91_);
lean_inc(v_bkt_106_);
v___x_113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_113_, 0, v_a_89_);
lean_ctor_set(v___x_113_, 1, v_b_90_);
lean_ctor_set(v___x_113_, 2, v_bkt_106_);
v_buckets_x27_114_ = lean_array_uset(v_buckets_92_, v___x_105_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(4u);
v___x_116_ = lean_nat_mul(v_size_x27_112_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = lean_nat_div(v___x_116_, v___x_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_array_get_size(v_buckets_x27_114_);
v___x_120_ = lean_nat_dec_le(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
if (v___x_120_ == 0)
{
lean_object* v_val_121_; lean_object* v___x_123_; 
v_val_121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2___redArg(v_buckets_x27_114_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_val_121_);
lean_ctor_set(v___x_109_, 0, v_size_x27_112_);
v___x_123_ = v___x_109_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_size_x27_112_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_val_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v___x_126_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_buckets_x27_114_);
lean_ctor_set(v___x_109_, 0, v_size_x27_112_);
v___x_126_ = v___x_109_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_size_x27_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_buckets_x27_114_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_dec(v_b_90_);
lean_dec_ref(v_a_89_);
return v_m_88_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object* v_m_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_buckets_133_; lean_object* v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_buckets_133_ = lean_ctor_get(v_m_131_, 1);
v___x_134_ = lean_array_get_size(v_buckets_133_);
v___x_135_ = l_Lean_Expr_hash(v_a_132_);
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___x_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___x_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_134_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v___x_147_ = lean_array_uget_borrowed(v_buckets_133_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_132_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg___boxed(lean_object* v_m_149_, lean_object* v_a_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_149_, v_a_150_);
lean_dec_ref(v_a_150_);
lean_dec_ref(v_m_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* v_x_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_d_156_; lean_object* v_b_157_; lean_object* v___y_158_; 
switch(lean_obj_tag(v_x_153_))
{
case 11:
{
lean_object* v_struct_161_; lean_object* v___x_162_; 
v_struct_161_ = lean_ctor_get(v_x_153_, 2);
lean_inc_ref(v_struct_161_);
lean_dec_ref_known(v_x_153_, 3);
v___x_162_ = l_Lean_CollectFVars_visit(v_struct_161_, v_a_154_);
return v___x_162_;
}
case 7:
{
lean_object* v_binderType_163_; lean_object* v_body_164_; 
v_binderType_163_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_binderType_163_);
v_body_164_ = lean_ctor_get(v_x_153_, 2);
lean_inc_ref(v_body_164_);
lean_dec_ref_known(v_x_153_, 3);
v_d_156_ = v_binderType_163_;
v_b_157_ = v_body_164_;
v___y_158_ = v_a_154_;
goto v___jp_155_;
}
case 6:
{
lean_object* v_binderType_165_; lean_object* v_body_166_; 
v_binderType_165_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_binderType_165_);
v_body_166_ = lean_ctor_get(v_x_153_, 2);
lean_inc_ref(v_body_166_);
lean_dec_ref_known(v_x_153_, 3);
v_d_156_ = v_binderType_165_;
v_b_157_ = v_body_166_;
v___y_158_ = v_a_154_;
goto v___jp_155_;
}
case 8:
{
lean_object* v_type_167_; lean_object* v_value_168_; lean_object* v_body_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_type_167_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_type_167_);
v_value_168_ = lean_ctor_get(v_x_153_, 2);
lean_inc_ref(v_value_168_);
v_body_169_ = lean_ctor_get(v_x_153_, 3);
lean_inc_ref(v_body_169_);
lean_dec_ref_known(v_x_153_, 4);
v___x_170_ = l_Lean_CollectFVars_visit(v_type_167_, v_a_154_);
v___x_171_ = l_Lean_CollectFVars_visit(v_value_168_, v___x_170_);
v___x_172_ = l_Lean_CollectFVars_visit(v_body_169_, v___x_171_);
return v___x_172_;
}
case 5:
{
lean_object* v_fn_173_; lean_object* v_arg_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_fn_173_ = lean_ctor_get(v_x_153_, 0);
lean_inc_ref(v_fn_173_);
v_arg_174_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_arg_174_);
lean_dec_ref_known(v_x_153_, 2);
v___x_175_ = l_Lean_CollectFVars_visit(v_fn_173_, v_a_154_);
v___x_176_ = l_Lean_CollectFVars_visit(v_arg_174_, v___x_175_);
return v___x_176_;
}
case 10:
{
lean_object* v_expr_177_; lean_object* v___x_178_; 
v_expr_177_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_expr_177_);
lean_dec_ref_known(v_x_153_, 2);
v___x_178_ = l_Lean_CollectFVars_visit(v_expr_177_, v_a_154_);
return v___x_178_;
}
case 1:
{
lean_object* v_fvarId_179_; lean_object* v___x_180_; 
v_fvarId_179_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_fvarId_179_);
lean_dec_ref_known(v_x_153_, 1);
v___x_180_ = l_Lean_CollectFVars_State_add(v_a_154_, v_fvarId_179_);
return v___x_180_;
}
default: 
{
lean_dec_ref(v_x_153_);
return v_a_154_;
}
}
v___jp_155_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = l_Lean_CollectFVars_visit(v_d_156_, v___y_158_);
v___x_160_ = l_Lean_CollectFVars_visit(v_b_157_, v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* v_e_181_, lean_object* v_s_182_){
_start:
{
uint8_t v___y_184_; uint8_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = l_Lean_Expr_hasFVar(v_e_181_);
v___x_199_ = lean_bool_not(v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v_visitedExpr_200_; uint8_t v___x_201_; 
v_visitedExpr_200_ = lean_ctor_get(v_s_182_, 0);
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visitedExpr_200_, v_e_181_);
v___y_184_ = v___x_201_;
goto v___jp_183_;
}
else
{
v___y_184_ = v___x_199_;
goto v___jp_183_;
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
lean_object* v_visitedExpr_185_; lean_object* v_fvarSet_186_; lean_object* v_fvarIds_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_visitedExpr_185_ = lean_ctor_get(v_s_182_, 0);
v_fvarSet_186_ = lean_ctor_get(v_s_182_, 1);
v_fvarIds_187_ = lean_ctor_get(v_s_182_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_s_182_);
if (v_isSharedCheck_197_ == 0)
{
v___x_189_ = v_s_182_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_fvarIds_187_);
lean_inc(v_fvarSet_186_);
lean_inc(v_visitedExpr_185_);
lean_dec(v_s_182_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_box(0);
lean_inc_ref(v_e_181_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visitedExpr_185_, v_e_181_, v___x_191_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_fvarSet_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_fvarIds_187_);
v___x_194_ = v_reuseFailAlloc_196_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_CollectFVars_main(v_e_181_, v___x_194_);
return v___x_195_;
}
}
}
else
{
lean_dec_ref(v_e_181_);
return v_s_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0(lean_object* v_00_u03b2_202_, lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_203_, v_a_204_, v_b_205_);
return v___x_206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1(lean_object* v_00_u03b2_207_, lean_object* v_m_208_, lean_object* v_a_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_208_, v_a_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1___boxed(lean_object* v_00_u03b2_211_, lean_object* v_m_212_, lean_object* v_a_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__1(v_00_u03b2_211_, v_m_212_, v_a_213_);
lean_dec_ref(v_a_213_);
lean_dec_ref(v_m_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_216_, lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_217_, v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_220_, lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__1(v_00_u03b2_220_, v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec_ref(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2(lean_object* v_00_u03b2_225_, lean_object* v_data_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2___redArg(v_data_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_228_, lean_object* v_i_229_, lean_object* v_source_230_, lean_object* v_target_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3___redArg(v_i_229_, v_source_230_, v_target_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(v_x_234_, v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object* v_s_237_, lean_object* v_e_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_CollectFVars_main(v_e_238_, v_s_237_);
return v___x_239_;
}
}
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_instInhabitedState_default = _init_l_Lean_CollectFVars_instInhabitedState_default();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState_default);
l_Lean_CollectFVars_instInhabitedState = _init_l_Lean_CollectFVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectFVars(builtin);
}
#ifdef __cplusplus
}
#endif
