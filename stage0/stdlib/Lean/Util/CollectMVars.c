// Lean compiler output
// Module: Lean.Util.CollectMVars
// Imports: public import Lean.Expr public import Lean.Meta.Sym.ExprPtr
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
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CollectMVars_State_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_State_empty___closed__0;
static lean_once_cell_t l_Lean_CollectMVars_State_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_State_empty___closed__1;
static const lean_array_object l_Lean_CollectMVars_State_empty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectMVars_State_empty___closed__2 = (const lean_object*)&l_Lean_CollectMVars_State_empty___closed__2_value;
static lean_once_cell_t l_Lean_CollectMVars_State_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_State_empty___closed__3;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_State_empty;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_instEmptyCollectionState;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectMVars_State_empty___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_empty___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectMVars_State_empty___closed__0, &l_Lean_CollectMVars_State_empty___closed__0_once, _init_l_Lean_CollectMVars_State_empty___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_empty___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l_Lean_CollectMVars_State_empty___closed__2));
v___x_10_ = lean_box(1);
v___x_11_ = lean_obj_once(&l_Lean_CollectMVars_State_empty___closed__1, &l_Lean_CollectMVars_State_empty___closed__1_once, _init_l_Lean_CollectMVars_State_empty___closed__1);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_CollectMVars_State_empty(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_CollectMVars_State_empty___closed__3, &l_Lean_CollectMVars_State_empty___closed__3_once, _init_l_Lean_CollectMVars_State_empty___closed__3);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instEmptyCollectionState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_CollectMVars_State_empty;
return v___x_14_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_CollectMVars_State_empty;
return v___x_15_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
else
{
lean_object* v_key_19_; lean_object* v_tail_20_; size_t v___x_21_; size_t v___x_22_; uint8_t v___x_23_; 
v_key_19_ = lean_ctor_get(v_x_17_, 0);
v_tail_20_ = lean_ctor_get(v_x_17_, 2);
v___x_21_ = lean_ptr_addr(v_key_19_);
v___x_22_ = lean_ptr_addr(v_a_16_);
v___x_23_ = lean_usize_dec_eq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
v_x_17_ = v_tail_20_;
goto _start;
}
else
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(v_a_25_, v_x_26_);
lean_dec(v_x_26_);
lean_dec_ref(v_a_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object* v_m_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_buckets_31_; lean_object* v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v_fold_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; size_t v___x_43_; size_t v___x_44_; size_t v___x_45_; size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_buckets_31_ = lean_ctor_get(v_m_29_, 1);
v___x_32_ = lean_array_get_size(v_buckets_31_);
v___x_33_ = lean_ptr_addr(v_a_30_);
v___x_34_ = ((size_t)3ULL);
v___x_35_ = lean_usize_shift_right(v___x_33_, v___x_34_);
v___x_36_ = lean_usize_to_uint64(v___x_35_);
v___x_37_ = 32ULL;
v___x_38_ = lean_uint64_shift_right(v___x_36_, v___x_37_);
v_fold_39_ = lean_uint64_xor(v___x_36_, v___x_38_);
v___x_40_ = 16ULL;
v___x_41_ = lean_uint64_shift_right(v_fold_39_, v___x_40_);
v___x_42_ = lean_uint64_xor(v_fold_39_, v___x_41_);
v___x_43_ = lean_uint64_to_usize(v___x_42_);
v___x_44_ = lean_usize_of_nat(v___x_32_);
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_sub(v___x_44_, v___x_45_);
v___x_47_ = lean_usize_land(v___x_43_, v___x_46_);
v___x_48_ = lean_array_uget_borrowed(v_buckets_31_, v___x_47_);
v___x_49_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(v_a_30_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object* v_m_50_, lean_object* v_a_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_50_, v_a_51_);
lean_dec_ref(v_a_51_);
lean_dec_ref(v_m_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg(lean_object* v_k_54_, lean_object* v_t_55_){
_start:
{
if (lean_obj_tag(v_t_55_) == 0)
{
lean_object* v_k_56_; lean_object* v_l_57_; lean_object* v_r_58_; uint8_t v___x_59_; 
v_k_56_ = lean_ctor_get(v_t_55_, 1);
v_l_57_ = lean_ctor_get(v_t_55_, 3);
v_r_58_ = lean_ctor_get(v_t_55_, 4);
v___x_59_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_54_, v_k_56_);
switch(v___x_59_)
{
case 0:
{
v_t_55_ = v_l_57_;
goto _start;
}
case 1:
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
default: 
{
v_t_55_ = v_r_58_;
goto _start;
}
}
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg___boxed(lean_object* v_k_64_, lean_object* v_t_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg(v_k_64_, v_t_65_);
lean_dec(v_t_65_);
lean_dec(v_k_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
return v_x_68_;
}
else
{
lean_object* v_key_70_; lean_object* v_value_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_98_; 
v_key_70_ = lean_ctor_get(v_x_69_, 0);
v_value_71_ = lean_ctor_get(v_x_69_, 1);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_98_ == 0)
{
v___x_74_ = v_x_69_;
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_value_71_);
lean_inc(v_key_70_);
lean_dec(v_x_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; uint64_t v_fold_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_76_ = lean_array_get_size(v_x_68_);
v___x_77_ = lean_ptr_addr(v_key_70_);
v___x_78_ = ((size_t)3ULL);
v___x_79_ = lean_usize_shift_right(v___x_77_, v___x_78_);
v___x_80_ = lean_usize_to_uint64(v___x_79_);
v___x_81_ = 32ULL;
v___x_82_ = lean_uint64_shift_right(v___x_80_, v___x_81_);
v_fold_83_ = lean_uint64_xor(v___x_80_, v___x_82_);
v___x_84_ = 16ULL;
v___x_85_ = lean_uint64_shift_right(v_fold_83_, v___x_84_);
v___x_86_ = lean_uint64_xor(v_fold_83_, v___x_85_);
v___x_87_ = lean_uint64_to_usize(v___x_86_);
v___x_88_ = lean_usize_of_nat(v___x_76_);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_sub(v___x_88_, v___x_89_);
v___x_91_ = lean_usize_land(v___x_87_, v___x_90_);
v___x_92_ = lean_array_uget_borrowed(v_x_68_, v___x_91_);
lean_inc(v___x_92_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 2, v___x_92_);
v___x_94_ = v___x_74_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_key_70_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_value_71_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_97_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = lean_array_uset(v_x_68_, v___x_91_, v___x_94_);
v_x_68_ = v___x_95_;
v_x_69_ = v_tail_72_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4___redArg(lean_object* v_i_99_, lean_object* v_source_100_, lean_object* v_target_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_array_get_size(v_source_100_);
v___x_103_ = lean_nat_dec_lt(v_i_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec_ref(v_source_100_);
lean_dec(v_i_99_);
return v_target_101_;
}
else
{
lean_object* v_es_104_; lean_object* v___x_105_; lean_object* v_source_106_; lean_object* v_target_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_es_104_ = lean_array_fget(v_source_100_, v_i_99_);
v___x_105_ = lean_box(0);
v_source_106_ = lean_array_fset(v_source_100_, v_i_99_, v___x_105_);
v_target_107_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(v_target_101_, v_es_104_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_i_99_, v___x_108_);
lean_dec(v_i_99_);
v_i_99_ = v___x_109_;
v_source_100_ = v_source_106_;
v_target_101_ = v_target_107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2___redArg(lean_object* v_data_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_nbuckets_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_112_ = lean_array_get_size(v_data_111_);
v___x_113_ = lean_unsigned_to_nat(2u);
v_nbuckets_114_ = lean_nat_mul(v___x_112_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_box(0);
v___x_117_ = lean_mk_array(v_nbuckets_114_, v___x_116_);
v___x_118_ = lean_array_propagate_mark(v_data_111_, v___x_117_);
v___x_119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4___redArg(v___x_115_, v_data_111_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object* v_m_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
lean_object* v_size_123_; lean_object* v_buckets_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v_fold_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_bkt_141_; uint8_t v___x_142_; 
v_size_123_ = lean_ctor_get(v_m_120_, 0);
v_buckets_124_ = lean_ctor_get(v_m_120_, 1);
v___x_125_ = lean_array_get_size(v_buckets_124_);
v___x_126_ = lean_ptr_addr(v_a_121_);
v___x_127_ = ((size_t)3ULL);
v___x_128_ = lean_usize_shift_right(v___x_126_, v___x_127_);
v___x_129_ = lean_usize_to_uint64(v___x_128_);
v___x_130_ = 32ULL;
v___x_131_ = lean_uint64_shift_right(v___x_129_, v___x_130_);
v_fold_132_ = lean_uint64_xor(v___x_129_, v___x_131_);
v___x_133_ = 16ULL;
v___x_134_ = lean_uint64_shift_right(v_fold_132_, v___x_133_);
v___x_135_ = lean_uint64_xor(v_fold_132_, v___x_134_);
v___x_136_ = lean_uint64_to_usize(v___x_135_);
v___x_137_ = lean_usize_of_nat(v___x_125_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_sub(v___x_137_, v___x_138_);
v___x_140_ = lean_usize_land(v___x_136_, v___x_139_);
v_bkt_141_ = lean_array_uget_borrowed(v_buckets_124_, v___x_140_);
v___x_142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(v_a_121_, v_bkt_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_163_; 
lean_inc_ref(v_buckets_124_);
lean_inc(v_size_123_);
v_isSharedCheck_163_ = !lean_is_exclusive(v_m_120_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_164_ = lean_ctor_get(v_m_120_, 1);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_m_120_, 0);
lean_dec(v_unused_165_);
v___x_144_ = v_m_120_;
v_isShared_145_ = v_isSharedCheck_163_;
goto v_resetjp_143_;
}
else
{
lean_dec(v_m_120_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_163_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v_size_x27_147_; lean_object* v___x_148_; lean_object* v_buckets_x27_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v_size_x27_147_ = lean_nat_add(v_size_123_, v___x_146_);
lean_dec(v_size_123_);
lean_inc(v_bkt_141_);
v___x_148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_148_, 0, v_a_121_);
lean_ctor_set(v___x_148_, 1, v_b_122_);
lean_ctor_set(v___x_148_, 2, v_bkt_141_);
v_buckets_x27_149_ = lean_array_uset(v_buckets_124_, v___x_140_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(4u);
v___x_151_ = lean_nat_mul(v_size_x27_147_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(3u);
v___x_153_ = lean_nat_div(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_array_get_size(v_buckets_x27_149_);
v___x_155_ = lean_nat_dec_le(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v_val_156_; lean_object* v___x_158_; 
v_val_156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2___redArg(v_buckets_x27_149_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v_val_156_);
lean_ctor_set(v___x_144_, 0, v_size_x27_147_);
v___x_158_ = v___x_144_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_val_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_161_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v_buckets_x27_149_);
lean_ctor_set(v___x_144_, 0, v_size_x27_147_);
v___x_161_ = v___x_144_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_buckets_x27_149_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_dec(v_b_122_);
lean_dec_ref(v_a_121_);
return v_m_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object* v_x_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_d_169_; lean_object* v_b_170_; lean_object* v___y_171_; 
switch(lean_obj_tag(v_x_166_))
{
case 11:
{
lean_object* v_struct_174_; lean_object* v___x_175_; 
v_struct_174_ = lean_ctor_get(v_x_166_, 2);
lean_inc_ref(v_struct_174_);
lean_dec_ref_known(v_x_166_, 3);
v___x_175_ = l_Lean_CollectMVars_visit(v_struct_174_, v_a_167_);
return v___x_175_;
}
case 7:
{
lean_object* v_binderType_176_; lean_object* v_body_177_; 
v_binderType_176_ = lean_ctor_get(v_x_166_, 1);
lean_inc_ref(v_binderType_176_);
v_body_177_ = lean_ctor_get(v_x_166_, 2);
lean_inc_ref(v_body_177_);
lean_dec_ref_known(v_x_166_, 3);
v_d_169_ = v_binderType_176_;
v_b_170_ = v_body_177_;
v___y_171_ = v_a_167_;
goto v___jp_168_;
}
case 6:
{
lean_object* v_binderType_178_; lean_object* v_body_179_; 
v_binderType_178_ = lean_ctor_get(v_x_166_, 1);
lean_inc_ref(v_binderType_178_);
v_body_179_ = lean_ctor_get(v_x_166_, 2);
lean_inc_ref(v_body_179_);
lean_dec_ref_known(v_x_166_, 3);
v_d_169_ = v_binderType_178_;
v_b_170_ = v_body_179_;
v___y_171_ = v_a_167_;
goto v___jp_168_;
}
case 8:
{
lean_object* v_type_180_; lean_object* v_value_181_; lean_object* v_body_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_type_180_ = lean_ctor_get(v_x_166_, 1);
lean_inc_ref(v_type_180_);
v_value_181_ = lean_ctor_get(v_x_166_, 2);
lean_inc_ref(v_value_181_);
v_body_182_ = lean_ctor_get(v_x_166_, 3);
lean_inc_ref(v_body_182_);
lean_dec_ref_known(v_x_166_, 4);
v___x_183_ = l_Lean_CollectMVars_visit(v_type_180_, v_a_167_);
v___x_184_ = l_Lean_CollectMVars_visit(v_value_181_, v___x_183_);
v___x_185_ = l_Lean_CollectMVars_visit(v_body_182_, v___x_184_);
return v___x_185_;
}
case 5:
{
lean_object* v_fn_186_; lean_object* v_arg_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_fn_186_ = lean_ctor_get(v_x_166_, 0);
lean_inc_ref(v_fn_186_);
v_arg_187_ = lean_ctor_get(v_x_166_, 1);
lean_inc_ref(v_arg_187_);
lean_dec_ref_known(v_x_166_, 2);
v___x_188_ = l_Lean_CollectMVars_visit(v_fn_186_, v_a_167_);
v___x_189_ = l_Lean_CollectMVars_visit(v_arg_187_, v___x_188_);
return v___x_189_;
}
case 10:
{
lean_object* v_expr_190_; lean_object* v___x_191_; 
v_expr_190_ = lean_ctor_get(v_x_166_, 1);
lean_inc_ref(v_expr_190_);
lean_dec_ref_known(v_x_166_, 2);
v___x_191_ = l_Lean_CollectMVars_visit(v_expr_190_, v_a_167_);
return v___x_191_;
}
case 2:
{
lean_object* v_mvarId_192_; lean_object* v_visited_193_; lean_object* v_mvarSet_194_; lean_object* v_result_195_; uint8_t v___x_196_; 
v_mvarId_192_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_mvarId_192_);
lean_dec_ref_known(v_x_166_, 1);
v_visited_193_ = lean_ctor_get(v_a_167_, 0);
v_mvarSet_194_ = lean_ctor_get(v_a_167_, 1);
v_result_195_ = lean_ctor_get(v_a_167_, 2);
v___x_196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg(v_mvarId_192_, v_mvarSet_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
lean_inc_ref(v_result_195_);
lean_inc(v_mvarSet_194_);
lean_inc_ref(v_visited_193_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_a_167_, 2);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_a_167_, 1);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_a_167_, 0);
lean_dec(v_unused_208_);
v___x_198_ = v_a_167_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_a_167_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
lean_inc(v_mvarId_192_);
v___x_200_ = l_Lean_MVarIdSet_insert(v_mvarSet_194_, v_mvarId_192_);
v___x_201_ = lean_array_push(v_result_195_, v_mvarId_192_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 2, v___x_201_);
lean_ctor_set(v___x_198_, 1, v___x_200_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_visited_193_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_dec(v_mvarId_192_);
return v_a_167_;
}
}
default: 
{
lean_dec_ref(v_x_166_);
return v_a_167_;
}
}
v___jp_168_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_CollectMVars_visit(v_d_169_, v___y_171_);
v___x_173_ = l_Lean_CollectMVars_visit(v_b_170_, v___x_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object* v_e_209_, lean_object* v_s_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Lean_Expr_hasExprMVar(v_e_209_);
if (v___x_211_ == 0)
{
lean_dec_ref(v_e_209_);
return v_s_210_;
}
else
{
lean_object* v_visited_212_; lean_object* v_mvarSet_213_; lean_object* v_result_214_; uint8_t v___x_215_; 
v_visited_212_ = lean_ctor_get(v_s_210_, 0);
v_mvarSet_213_ = lean_ctor_get(v_s_210_, 1);
v_result_214_ = lean_ctor_get(v_s_210_, 2);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_visited_212_, v_e_209_);
if (v___x_215_ == 0)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
lean_inc_ref(v_result_214_);
lean_inc(v_mvarSet_213_);
lean_inc_ref(v_visited_212_);
v_isSharedCheck_225_ = !lean_is_exclusive(v_s_210_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_226_ = lean_ctor_get(v_s_210_, 2);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_s_210_, 1);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_s_210_, 0);
lean_dec(v_unused_228_);
v___x_217_ = v_s_210_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_s_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_219_ = lean_box(0);
lean_inc_ref(v_e_209_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_visited_212_, v_e_209_, v___x_219_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_mvarSet_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_result_214_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_CollectMVars_main(v_e_209_, v___x_222_);
return v___x_223_;
}
}
}
else
{
lean_dec_ref(v_e_209_);
return v_s_210_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object* v_00_u03b2_229_, lean_object* v_m_230_, lean_object* v_a_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_230_, v_a_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object* v_00_u03b2_233_, lean_object* v_m_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(v_00_u03b2_233_, v_m_234_, v_a_235_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_m_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1(lean_object* v_00_u03b2_238_, lean_object* v_m_239_, lean_object* v_a_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_239_, v_a_240_, v_b_241_);
return v___x_242_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3(lean_object* v_00_u03b2_243_, lean_object* v_k_244_, lean_object* v_t_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___redArg(v_k_244_, v_t_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3___boxed(lean_object* v_00_u03b2_247_, lean_object* v_k_248_, lean_object* v_t_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectMVars_main_spec__3(v_00_u03b2_247_, v_k_248_, v_t_249_);
lean_dec(v_t_249_);
lean_dec(v_k_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0(lean_object* v_00_u03b2_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___redArg(v_a_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_256_, lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__0(v_00_u03b2_256_, v_a_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec_ref(v_a_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2(lean_object* v_00_u03b2_261_, lean_object* v_data_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2___redArg(v_data_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_264_, lean_object* v_i_265_, lean_object* v_source_266_, lean_object* v_target_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4___redArg(v_i_265_, v_source_266_, v_target_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(v_x_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object* v_s_273_, lean_object* v_e_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_CollectMVars_visit(v_e_274_, v_s_273_);
return v___x_275_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectMVars_State_empty = _init_l_Lean_CollectMVars_State_empty();
lean_mark_persistent(l_Lean_CollectMVars_State_empty);
l_Lean_CollectMVars_instEmptyCollectionState = _init_l_Lean_CollectMVars_instEmptyCollectionState();
lean_mark_persistent(l_Lean_CollectMVars_instEmptyCollectionState);
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
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
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
