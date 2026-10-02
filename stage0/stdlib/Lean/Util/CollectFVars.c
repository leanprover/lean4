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
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object* v_a_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
else
{
lean_object* v_key_32_; lean_object* v_tail_33_; uint8_t v___x_34_; 
v_key_32_ = lean_ctor_get(v_x_30_, 0);
v_tail_33_ = lean_ctor_get(v_x_30_, 2);
v___x_34_ = lean_expr_eqv(v_key_32_, v_a_29_);
if (v___x_34_ == 0)
{
v_x_30_ = v_tail_33_;
goto _start;
}
else
{
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_36_, v_x_37_);
lean_dec(v_x_37_);
lean_dec_ref(v_a_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
return v_x_40_;
}
else
{
lean_object* v_key_42_; lean_object* v_value_43_; lean_object* v_tail_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_67_; 
v_key_42_ = lean_ctor_get(v_x_41_, 0);
v_value_43_ = lean_ctor_get(v_x_41_, 1);
v_tail_44_ = lean_ctor_get(v_x_41_, 2);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_67_ == 0)
{
v___x_46_ = v_x_41_;
v_isShared_47_ = v_isSharedCheck_67_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_tail_44_);
lean_inc(v_value_43_);
lean_inc(v_key_42_);
lean_dec(v_x_41_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_67_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v_fold_52_; uint64_t v___x_53_; uint64_t v___x_54_; uint64_t v___x_55_; size_t v___x_56_; size_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_48_ = lean_array_get_size(v_x_40_);
v___x_49_ = l_Lean_Expr_hash(v_key_42_);
v___x_50_ = 32ULL;
v___x_51_ = lean_uint64_shift_right(v___x_49_, v___x_50_);
v_fold_52_ = lean_uint64_xor(v___x_49_, v___x_51_);
v___x_53_ = 16ULL;
v___x_54_ = lean_uint64_shift_right(v_fold_52_, v___x_53_);
v___x_55_ = lean_uint64_xor(v_fold_52_, v___x_54_);
v___x_56_ = lean_uint64_to_usize(v___x_55_);
v___x_57_ = lean_usize_of_nat(v___x_48_);
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_sub(v___x_57_, v___x_58_);
v___x_60_ = lean_usize_land(v___x_56_, v___x_59_);
v___x_61_ = lean_array_uget_borrowed(v_x_40_, v___x_60_);
lean_inc(v___x_61_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 2, v___x_61_);
v___x_63_ = v___x_46_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_key_42_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_value_43_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v___x_61_);
v___x_63_ = v_reuseFailAlloc_66_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; 
v___x_64_ = lean_array_uset(v_x_40_, v___x_60_, v___x_63_);
v_x_40_ = v___x_64_;
v_x_41_ = v_tail_44_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(lean_object* v_i_68_, lean_object* v_source_69_, lean_object* v_target_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_array_get_size(v_source_69_);
v___x_72_ = lean_nat_dec_lt(v_i_68_, v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_source_69_);
lean_dec(v_i_68_);
return v_target_70_;
}
else
{
lean_object* v_es_73_; lean_object* v___x_74_; lean_object* v_source_75_; lean_object* v_target_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_es_73_ = lean_array_fget(v_source_69_, v_i_68_);
v___x_74_ = lean_box(0);
v_source_75_ = lean_array_fset(v_source_69_, v_i_68_, v___x_74_);
v_target_76_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_target_70_, v_es_73_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_i_68_, v___x_77_);
lean_dec(v_i_68_);
v_i_68_ = v___x_78_;
v_source_69_ = v_source_75_;
v_target_70_ = v_target_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(lean_object* v_data_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_nbuckets_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_81_ = lean_array_get_size(v_data_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v_nbuckets_83_ = lean_nat_mul(v___x_81_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_box(0);
v___x_86_ = lean_mk_array(v_nbuckets_83_, v___x_85_);
v___x_87_ = lean_array_propagate_mark(v_data_80_, v___x_86_);
v___x_88_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v___x_84_, v_data_80_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object* v_m_89_, lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_size_92_; lean_object* v_buckets_93_; lean_object* v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v_fold_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; lean_object* v_bkt_107_; uint8_t v___x_108_; 
v_size_92_ = lean_ctor_get(v_m_89_, 0);
v_buckets_93_ = lean_ctor_get(v_m_89_, 1);
v___x_94_ = lean_array_get_size(v_buckets_93_);
v___x_95_ = l_Lean_Expr_hash(v_a_90_);
v___x_96_ = 32ULL;
v___x_97_ = lean_uint64_shift_right(v___x_95_, v___x_96_);
v_fold_98_ = lean_uint64_xor(v___x_95_, v___x_97_);
v___x_99_ = 16ULL;
v___x_100_ = lean_uint64_shift_right(v_fold_98_, v___x_99_);
v___x_101_ = lean_uint64_xor(v_fold_98_, v___x_100_);
v___x_102_ = lean_uint64_to_usize(v___x_101_);
v___x_103_ = lean_usize_of_nat(v___x_94_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_sub(v___x_103_, v___x_104_);
v___x_106_ = lean_usize_land(v___x_102_, v___x_105_);
v_bkt_107_ = lean_array_uget_borrowed(v_buckets_93_, v___x_106_);
v___x_108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_90_, v_bkt_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_129_; 
lean_inc_ref(v_buckets_93_);
lean_inc(v_size_92_);
v_isSharedCheck_129_ = !lean_is_exclusive(v_m_89_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; lean_object* v_unused_131_; 
v_unused_130_ = lean_ctor_get(v_m_89_, 1);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_m_89_, 0);
lean_dec(v_unused_131_);
v___x_110_ = v_m_89_;
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_m_89_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v_size_x27_113_; lean_object* v___x_114_; lean_object* v_buckets_x27_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v_size_x27_113_ = lean_nat_add(v_size_92_, v___x_112_);
lean_dec(v_size_92_);
lean_inc(v_bkt_107_);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v_a_90_);
lean_ctor_set(v___x_114_, 1, v_b_91_);
lean_ctor_set(v___x_114_, 2, v_bkt_107_);
v_buckets_x27_115_ = lean_array_uset(v_buckets_93_, v___x_106_, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(4u);
v___x_117_ = lean_nat_mul(v_size_x27_113_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(3u);
v___x_119_ = lean_nat_div(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_array_get_size(v_buckets_x27_115_);
v___x_121_ = lean_nat_dec_le(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
if (v___x_121_ == 0)
{
lean_object* v_val_122_; lean_object* v___x_124_; 
v_val_122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_buckets_x27_115_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v_val_122_);
lean_ctor_set(v___x_110_, 0, v_size_x27_113_);
v___x_124_ = v___x_110_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_size_x27_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_val_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_127_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v_buckets_x27_115_);
lean_ctor_set(v___x_110_, 0, v_size_x27_113_);
v___x_127_ = v___x_110_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_size_x27_113_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_buckets_x27_115_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_dec(v_b_91_);
lean_dec_ref(v_a_90_);
return v_m_89_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_buckets_134_; lean_object* v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v_fold_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_buckets_134_ = lean_ctor_get(v_m_132_, 1);
v___x_135_ = lean_array_get_size(v_buckets_134_);
v___x_136_ = l_Lean_Expr_hash(v_a_133_);
v___x_137_ = 32ULL;
v___x_138_ = lean_uint64_shift_right(v___x_136_, v___x_137_);
v_fold_139_ = lean_uint64_xor(v___x_136_, v___x_138_);
v___x_140_ = 16ULL;
v___x_141_ = lean_uint64_shift_right(v_fold_139_, v___x_140_);
v___x_142_ = lean_uint64_xor(v_fold_139_, v___x_141_);
v___x_143_ = lean_uint64_to_usize(v___x_142_);
v___x_144_ = lean_usize_of_nat(v___x_135_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_sub(v___x_144_, v___x_145_);
v___x_147_ = lean_usize_land(v___x_143_, v___x_146_);
v___x_148_ = lean_array_uget_borrowed(v_buckets_134_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_133_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object* v_m_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_150_, v_a_151_);
lean_dec_ref(v_a_151_);
lean_dec_ref(v_m_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* v_x_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_d_157_; lean_object* v_b_158_; lean_object* v___y_159_; 
switch(lean_obj_tag(v_x_154_))
{
case 11:
{
lean_object* v_struct_162_; lean_object* v___x_163_; 
v_struct_162_ = lean_ctor_get(v_x_154_, 2);
lean_inc_ref(v_struct_162_);
lean_dec_ref_known(v_x_154_, 3);
v___x_163_ = l_Lean_CollectFVars_visit(v_struct_162_, v_a_155_);
return v___x_163_;
}
case 7:
{
lean_object* v_binderType_164_; lean_object* v_body_165_; 
v_binderType_164_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_binderType_164_);
v_body_165_ = lean_ctor_get(v_x_154_, 2);
lean_inc_ref(v_body_165_);
lean_dec_ref_known(v_x_154_, 3);
v_d_157_ = v_binderType_164_;
v_b_158_ = v_body_165_;
v___y_159_ = v_a_155_;
goto v___jp_156_;
}
case 6:
{
lean_object* v_binderType_166_; lean_object* v_body_167_; 
v_binderType_166_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_binderType_166_);
v_body_167_ = lean_ctor_get(v_x_154_, 2);
lean_inc_ref(v_body_167_);
lean_dec_ref_known(v_x_154_, 3);
v_d_157_ = v_binderType_166_;
v_b_158_ = v_body_167_;
v___y_159_ = v_a_155_;
goto v___jp_156_;
}
case 8:
{
lean_object* v_type_168_; lean_object* v_value_169_; lean_object* v_body_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_type_168_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_type_168_);
v_value_169_ = lean_ctor_get(v_x_154_, 2);
lean_inc_ref(v_value_169_);
v_body_170_ = lean_ctor_get(v_x_154_, 3);
lean_inc_ref(v_body_170_);
lean_dec_ref_known(v_x_154_, 4);
v___x_171_ = l_Lean_CollectFVars_visit(v_type_168_, v_a_155_);
v___x_172_ = l_Lean_CollectFVars_visit(v_value_169_, v___x_171_);
v___x_173_ = l_Lean_CollectFVars_visit(v_body_170_, v___x_172_);
return v___x_173_;
}
case 5:
{
lean_object* v_fn_174_; lean_object* v_arg_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_fn_174_ = lean_ctor_get(v_x_154_, 0);
lean_inc_ref(v_fn_174_);
v_arg_175_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_arg_175_);
lean_dec_ref_known(v_x_154_, 2);
v___x_176_ = l_Lean_CollectFVars_visit(v_fn_174_, v_a_155_);
v___x_177_ = l_Lean_CollectFVars_visit(v_arg_175_, v___x_176_);
return v___x_177_;
}
case 10:
{
lean_object* v_expr_178_; lean_object* v___x_179_; 
v_expr_178_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_expr_178_);
lean_dec_ref_known(v_x_154_, 2);
v___x_179_ = l_Lean_CollectFVars_visit(v_expr_178_, v_a_155_);
return v___x_179_;
}
case 1:
{
lean_object* v_fvarId_180_; lean_object* v___x_181_; 
v_fvarId_180_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_fvarId_180_);
lean_dec_ref_known(v_x_154_, 1);
v___x_181_ = l_Lean_CollectFVars_State_add(v_a_155_, v_fvarId_180_);
return v___x_181_;
}
default: 
{
lean_dec_ref(v_x_154_);
return v_a_155_;
}
}
v___jp_156_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = l_Lean_CollectFVars_visit(v_d_157_, v___y_159_);
v___x_161_ = l_Lean_CollectFVars_visit(v_b_158_, v___x_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* v_e_182_, lean_object* v_s_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Expr_hasFVar(v_e_182_);
if (v___x_184_ == 0)
{
lean_dec_ref(v_e_182_);
return v_s_183_;
}
else
{
lean_object* v_visitedExpr_185_; lean_object* v_fvarSet_186_; lean_object* v_fvarIds_187_; uint8_t v___x_188_; 
v_visitedExpr_185_ = lean_ctor_get(v_s_183_, 0);
v_fvarSet_186_ = lean_ctor_get(v_s_183_, 1);
v_fvarIds_187_ = lean_ctor_get(v_s_183_, 2);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visitedExpr_185_, v_e_182_);
if (v___x_188_ == 0)
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_198_; 
lean_inc_ref(v_fvarIds_187_);
lean_inc(v_fvarSet_186_);
lean_inc_ref(v_visitedExpr_185_);
v_isSharedCheck_198_ = !lean_is_exclusive(v_s_183_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; 
v_unused_199_ = lean_ctor_get(v_s_183_, 2);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_s_183_, 1);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_s_183_, 0);
lean_dec(v_unused_201_);
v___x_190_ = v_s_183_;
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_s_183_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_198_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_192_ = lean_box(0);
lean_inc_ref(v_e_182_);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visitedExpr_185_, v_e_182_, v___x_192_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_195_ = v___x_190_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_fvarSet_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_fvarIds_187_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_CollectFVars_main(v_e_182_, v___x_195_);
return v___x_196_;
}
}
}
else
{
lean_dec_ref(v_e_182_);
return v_s_183_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object* v_00_u03b2_202_, lean_object* v_m_203_, lean_object* v_a_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_203_, v_a_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object* v_00_u03b2_206_, lean_object* v_m_207_, lean_object* v_a_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(v_00_u03b2_206_, v_m_207_, v_a_208_);
lean_dec_ref(v_a_208_);
lean_dec_ref(v_m_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(lean_object* v_00_u03b2_211_, lean_object* v_m_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_212_, v_a_213_, v_b_214_);
return v___x_215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_216_, lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_217_, v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_220_, lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(v_00_u03b2_220_, v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec_ref(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_225_, lean_object* v_data_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_data_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_228_, lean_object* v_i_229_, lean_object* v_source_230_, lean_object* v_target_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v_i_229_, v_source_230_, v_target_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_x_234_, v_x_235_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
