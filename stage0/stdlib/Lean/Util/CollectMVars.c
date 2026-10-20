// Lean compiler output
// Module: Lean.Util.CollectMVars
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__1;
static const lean_array_object l_Lean_CollectMVars_instInhabitedState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectMVars_instInhabitedState___closed__2 = (const lean_object*)&l_Lean_CollectMVars_instInhabitedState___closed__2_value;
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__0, &l_Lean_CollectMVars_instInhabitedState___closed__0_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lean_CollectMVars_instInhabitedState___closed__2));
v___x_10_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__1, &l_Lean_CollectMVars_instInhabitedState___closed__1_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__1);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__3, &l_Lean_CollectMVars_instInhabitedState___closed__3_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__3);
return v___x_12_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
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
v___x_18_ = lean_expr_eqv(v_key_16_, v_a_13_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec_ref(v_a_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object* v_m_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_buckets_26_; lean_object* v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v_fold_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_buckets_26_ = lean_ctor_get(v_m_24_, 1);
v___x_27_ = lean_array_get_size(v_buckets_26_);
v___x_28_ = l_Lean_Expr_hash(v_a_25_);
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
v___x_41_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_25_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object* v_m_42_, lean_object* v_a_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_42_, v_a_43_);
lean_dec_ref(v_a_43_);
lean_dec_ref(v_m_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_46_, lean_object* v_x_47_){
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
v___x_55_ = l_Lean_Expr_hash(v_key_48_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(lean_object* v_i_74_, lean_object* v_source_75_, lean_object* v_target_76_){
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
v_target_82_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_target_76_, v_es_79_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(lean_object* v_data_86_){
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
v___x_94_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(v___x_90_, v_data_86_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object* v_m_95_, lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
lean_object* v_size_98_; lean_object* v_buckets_99_; lean_object* v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v_fold_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v_bkt_113_; uint8_t v___x_114_; 
v_size_98_ = lean_ctor_get(v_m_95_, 0);
v_buckets_99_ = lean_ctor_get(v_m_95_, 1);
v___x_100_ = lean_array_get_size(v_buckets_99_);
v___x_101_ = l_Lean_Expr_hash(v_a_96_);
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
v___x_114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_96_, v_bkt_113_);
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
v_val_128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_buckets_x27_121_);
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
lean_dec_ref(v_a_96_);
return v_m_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object* v_x_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_d_141_; lean_object* v_b_142_; lean_object* v___y_143_; 
switch(lean_obj_tag(v_x_138_))
{
case 11:
{
lean_object* v_struct_146_; lean_object* v___x_147_; 
v_struct_146_ = lean_ctor_get(v_x_138_, 2);
lean_inc_ref(v_struct_146_);
lean_dec_ref_known(v_x_138_, 3);
v___x_147_ = l_Lean_CollectMVars_visit(v_struct_146_, v_a_139_);
return v___x_147_;
}
case 7:
{
lean_object* v_binderType_148_; lean_object* v_body_149_; 
v_binderType_148_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_binderType_148_);
v_body_149_ = lean_ctor_get(v_x_138_, 2);
lean_inc_ref(v_body_149_);
lean_dec_ref_known(v_x_138_, 3);
v_d_141_ = v_binderType_148_;
v_b_142_ = v_body_149_;
v___y_143_ = v_a_139_;
goto v___jp_140_;
}
case 6:
{
lean_object* v_binderType_150_; lean_object* v_body_151_; 
v_binderType_150_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_binderType_150_);
v_body_151_ = lean_ctor_get(v_x_138_, 2);
lean_inc_ref(v_body_151_);
lean_dec_ref_known(v_x_138_, 3);
v_d_141_ = v_binderType_150_;
v_b_142_ = v_body_151_;
v___y_143_ = v_a_139_;
goto v___jp_140_;
}
case 8:
{
lean_object* v_type_152_; lean_object* v_value_153_; lean_object* v_body_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_type_152_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_type_152_);
v_value_153_ = lean_ctor_get(v_x_138_, 2);
lean_inc_ref(v_value_153_);
v_body_154_ = lean_ctor_get(v_x_138_, 3);
lean_inc_ref(v_body_154_);
lean_dec_ref_known(v_x_138_, 4);
v___x_155_ = l_Lean_CollectMVars_visit(v_type_152_, v_a_139_);
v___x_156_ = l_Lean_CollectMVars_visit(v_value_153_, v___x_155_);
v___x_157_ = l_Lean_CollectMVars_visit(v_body_154_, v___x_156_);
return v___x_157_;
}
case 5:
{
lean_object* v_fn_158_; lean_object* v_arg_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_fn_158_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_fn_158_);
v_arg_159_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_arg_159_);
lean_dec_ref_known(v_x_138_, 2);
v___x_160_ = l_Lean_CollectMVars_visit(v_fn_158_, v_a_139_);
v___x_161_ = l_Lean_CollectMVars_visit(v_arg_159_, v___x_160_);
return v___x_161_;
}
case 10:
{
lean_object* v_expr_162_; lean_object* v___x_163_; 
v_expr_162_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_expr_162_);
lean_dec_ref_known(v_x_138_, 2);
v___x_163_ = l_Lean_CollectMVars_visit(v_expr_162_, v_a_139_);
return v___x_163_;
}
case 2:
{
lean_object* v_mvarId_164_; lean_object* v_visitedExpr_165_; lean_object* v_result_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_mvarId_164_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_mvarId_164_);
lean_dec_ref_known(v_x_138_, 1);
v_visitedExpr_165_ = lean_ctor_get(v_a_139_, 0);
v_result_166_ = lean_ctor_get(v_a_139_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_174_ == 0)
{
v___x_168_ = v_a_139_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_result_166_);
lean_inc(v_visitedExpr_165_);
lean_dec(v_a_139_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_array_push(v_result_166_, v_mvarId_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_visitedExpr_165_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
default: 
{
lean_dec_ref(v_x_138_);
return v_a_139_;
}
}
v___jp_140_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_Lean_CollectMVars_visit(v_d_141_, v___y_143_);
v___x_145_ = l_Lean_CollectMVars_visit(v_b_142_, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object* v_e_175_, lean_object* v_s_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Expr_hasExprMVar(v_e_175_);
if (v___x_177_ == 0)
{
lean_dec_ref(v_e_175_);
return v_s_176_;
}
else
{
lean_object* v_visitedExpr_178_; lean_object* v_result_179_; uint8_t v___x_180_; 
v_visitedExpr_178_ = lean_ctor_get(v_s_176_, 0);
v_result_179_ = lean_ctor_get(v_s_176_, 1);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_visitedExpr_178_, v_e_175_);
if (v___x_180_ == 0)
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_190_; 
lean_inc_ref(v_result_179_);
lean_inc_ref(v_visitedExpr_178_);
v_isSharedCheck_190_ = !lean_is_exclusive(v_s_176_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_191_ = lean_ctor_get(v_s_176_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_s_176_, 0);
lean_dec(v_unused_192_);
v___x_182_ = v_s_176_;
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_s_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_box(0);
lean_inc_ref(v_e_175_);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_visitedExpr_178_, v_e_175_, v___x_184_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_result_179_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_CollectMVars_main(v_e_175_, v___x_187_);
return v___x_188_;
}
}
}
else
{
lean_dec_ref(v_e_175_);
return v_s_176_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_194_, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(v_00_u03b2_197_, v_m_198_, v_a_199_);
lean_dec_ref(v_a_199_);
lean_dec_ref(v_m_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1(lean_object* v_00_u03b2_202_, lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_203_, v_a_204_, v_b_205_);
return v___x_206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_207_, lean_object* v_a_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_208_, v_x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_211_, lean_object* v_a_212_, lean_object* v_x_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(v_00_u03b2_211_, v_a_212_, v_x_213_);
lean_dec(v_x_213_);
lean_dec_ref(v_a_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_216_, lean_object* v_data_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_data_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_219_, lean_object* v_i_220_, lean_object* v_source_221_, lean_object* v_target_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(v_i_220_, v_source_221_, v_target_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_x_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object* v_s_228_, lean_object* v_e_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_CollectMVars_visit(v_e_229_, v_s_228_);
return v___x_230_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectMVars_instInhabitedState = _init_l_Lean_CollectMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectMVars(builtin);
}
#ifdef __cplusplus
}
#endif
