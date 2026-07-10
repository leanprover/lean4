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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_13_, lean_object* v_x_14_){
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
v___x_22_ = l_Lean_Expr_hash(v_key_15_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3___redArg(lean_object* v_i_41_, lean_object* v_source_42_, lean_object* v_target_43_){
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
v_target_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(v_target_43_, v_es_46_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2___redArg(lean_object* v_data_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_nbuckets_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_54_ = lean_array_get_size(v_data_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v_nbuckets_56_ = lean_nat_mul(v___x_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_box(0);
v___x_59_ = lean_mk_array(v_nbuckets_56_, v___x_58_);
v___x_60_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3___redArg(v___x_57_, v_data_53_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object* v_a_61_, lean_object* v_x_62_){
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
v___x_66_ = lean_expr_eqv(v_key_64_, v_a_61_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec_ref(v_a_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object* v_m_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v_size_75_; lean_object* v_buckets_76_; lean_object* v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v_fold_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v_bkt_90_; uint8_t v___x_91_; 
v_size_75_ = lean_ctor_get(v_m_72_, 0);
v_buckets_76_ = lean_ctor_get(v_m_72_, 1);
v___x_77_ = lean_array_get_size(v_buckets_76_);
v___x_78_ = l_Lean_Expr_hash(v_a_73_);
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
v___x_91_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_73_, v_bkt_90_);
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
v_val_105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2___redArg(v_buckets_x27_98_);
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
lean_dec_ref(v_a_73_);
return v_m_72_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_buckets_117_; lean_object* v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_buckets_117_ = lean_ctor_get(v_m_115_, 1);
v___x_118_ = lean_array_get_size(v_buckets_117_);
v___x_119_ = l_Lean_Expr_hash(v_a_116_);
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
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_116_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg___boxed(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_133_, v_a_134_);
lean_dec_ref(v_a_134_);
lean_dec_ref(v_m_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object* v_x_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_d_140_; lean_object* v_b_141_; lean_object* v___y_142_; 
switch(lean_obj_tag(v_x_137_))
{
case 11:
{
lean_object* v_struct_145_; lean_object* v___x_146_; 
v_struct_145_ = lean_ctor_get(v_x_137_, 2);
lean_inc_ref(v_struct_145_);
lean_dec_ref_known(v_x_137_, 3);
v___x_146_ = l_Lean_CollectMVars_visit(v_struct_145_, v_a_138_);
return v___x_146_;
}
case 7:
{
lean_object* v_binderType_147_; lean_object* v_body_148_; 
v_binderType_147_ = lean_ctor_get(v_x_137_, 1);
lean_inc_ref(v_binderType_147_);
v_body_148_ = lean_ctor_get(v_x_137_, 2);
lean_inc_ref(v_body_148_);
lean_dec_ref_known(v_x_137_, 3);
v_d_140_ = v_binderType_147_;
v_b_141_ = v_body_148_;
v___y_142_ = v_a_138_;
goto v___jp_139_;
}
case 6:
{
lean_object* v_binderType_149_; lean_object* v_body_150_; 
v_binderType_149_ = lean_ctor_get(v_x_137_, 1);
lean_inc_ref(v_binderType_149_);
v_body_150_ = lean_ctor_get(v_x_137_, 2);
lean_inc_ref(v_body_150_);
lean_dec_ref_known(v_x_137_, 3);
v_d_140_ = v_binderType_149_;
v_b_141_ = v_body_150_;
v___y_142_ = v_a_138_;
goto v___jp_139_;
}
case 8:
{
lean_object* v_type_151_; lean_object* v_value_152_; lean_object* v_body_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_type_151_ = lean_ctor_get(v_x_137_, 1);
lean_inc_ref(v_type_151_);
v_value_152_ = lean_ctor_get(v_x_137_, 2);
lean_inc_ref(v_value_152_);
v_body_153_ = lean_ctor_get(v_x_137_, 3);
lean_inc_ref(v_body_153_);
lean_dec_ref_known(v_x_137_, 4);
v___x_154_ = l_Lean_CollectMVars_visit(v_type_151_, v_a_138_);
v___x_155_ = l_Lean_CollectMVars_visit(v_value_152_, v___x_154_);
v___x_156_ = l_Lean_CollectMVars_visit(v_body_153_, v___x_155_);
return v___x_156_;
}
case 5:
{
lean_object* v_fn_157_; lean_object* v_arg_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_fn_157_ = lean_ctor_get(v_x_137_, 0);
lean_inc_ref(v_fn_157_);
v_arg_158_ = lean_ctor_get(v_x_137_, 1);
lean_inc_ref(v_arg_158_);
lean_dec_ref_known(v_x_137_, 2);
v___x_159_ = l_Lean_CollectMVars_visit(v_fn_157_, v_a_138_);
v___x_160_ = l_Lean_CollectMVars_visit(v_arg_158_, v___x_159_);
return v___x_160_;
}
case 10:
{
lean_object* v_expr_161_; lean_object* v___x_162_; 
v_expr_161_ = lean_ctor_get(v_x_137_, 1);
lean_inc_ref(v_expr_161_);
lean_dec_ref_known(v_x_137_, 2);
v___x_162_ = l_Lean_CollectMVars_visit(v_expr_161_, v_a_138_);
return v___x_162_;
}
case 2:
{
lean_object* v_mvarId_163_; lean_object* v_visitedExpr_164_; lean_object* v_result_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_mvarId_163_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_mvarId_163_);
lean_dec_ref_known(v_x_137_, 1);
v_visitedExpr_164_ = lean_ctor_get(v_a_138_, 0);
v_result_165_ = lean_ctor_get(v_a_138_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_a_138_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v_a_138_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_result_165_);
lean_inc(v_visitedExpr_164_);
lean_dec(v_a_138_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_array_push(v_result_165_, v_mvarId_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_visitedExpr_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
default: 
{
lean_dec_ref(v_x_137_);
return v_a_138_;
}
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Lean_CollectMVars_visit(v_d_140_, v___y_142_);
v___x_144_ = l_Lean_CollectMVars_visit(v_b_141_, v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object* v_e_174_, lean_object* v_s_175_){
_start:
{
uint8_t v___y_177_; uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = l_Lean_Expr_hasExprMVar(v_e_174_);
v___x_191_ = lean_bool_not(v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v_visitedExpr_192_; uint8_t v___x_193_; 
v_visitedExpr_192_ = lean_ctor_get(v_s_175_, 0);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg(v_visitedExpr_192_, v_e_174_);
v___y_177_ = v___x_193_;
goto v___jp_176_;
}
else
{
v___y_177_ = v___x_191_;
goto v___jp_176_;
}
v___jp_176_:
{
if (v___y_177_ == 0)
{
lean_object* v_visitedExpr_178_; lean_object* v_result_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_189_; 
v_visitedExpr_178_ = lean_ctor_get(v_s_175_, 0);
v_result_179_ = lean_ctor_get(v_s_175_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_s_175_);
if (v_isSharedCheck_189_ == 0)
{
v___x_181_ = v_s_175_;
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_result_179_);
lean_inc(v_visitedExpr_178_);
lean_dec(v_s_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = lean_box(0);
lean_inc_ref(v_e_174_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0___redArg(v_visitedExpr_178_, v_e_174_, v___x_183_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_result_179_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_CollectMVars_main(v_e_174_, v___x_186_);
return v___x_187_;
}
}
}
else
{
lean_dec_ref(v_e_174_);
return v_s_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0(lean_object* v_00_u03b2_194_, lean_object* v_m_195_, lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_195_, v_a_196_, v_b_197_);
return v___x_198_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1(lean_object* v_00_u03b2_199_, lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_200_, v_a_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1___boxed(lean_object* v_00_u03b2_203_, lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__1(v_00_u03b2_203_, v_m_204_, v_a_205_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_m_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_208_, lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_209_, v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_212_, lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__1(v_00_u03b2_212_, v_a_213_, v_x_214_);
lean_dec(v_x_214_);
lean_dec_ref(v_a_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2(lean_object* v_00_u03b2_217_, lean_object* v_data_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2___redArg(v_data_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_220_, lean_object* v_i_221_, lean_object* v_source_222_, lean_object* v_target_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3___redArg(v_i_221_, v_source_222_, v_target_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__0_spec__2_spec__3_spec__5___redArg(v_x_226_, v_x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object* v_s_229_, lean_object* v_e_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_CollectMVars_visit(v_e_230_, v_s_229_);
return v___x_231_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
