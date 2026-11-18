// Lean compiler output
// Module: Lean.Util.CollectFVars
// Imports: public import Lean.LocalContext public import Lean.Meta.Sym.ExprPtr
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CollectFVars_State_ofFVarSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_State_ofFVarSet___closed__0;
static lean_once_cell_t l_Lean_CollectFVars_State_ofFVarSet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_State_ofFVarSet___closed__1;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
static const lean_array_object l_Lean_CollectFVars_instEmptyCollectionState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectFVars_instEmptyCollectionState___closed__0 = (const lean_object*)&l_Lean_CollectFVars_instEmptyCollectionState___closed__0_value;
static lean_once_cell_t l_Lean_CollectFVars_instEmptyCollectionState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instEmptyCollectionState___closed__1;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instEmptyCollectionState;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectFVars_State_ofFVarSet___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_CollectFVars_State_ofFVarSet___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_CollectFVars_State_ofFVarSet___closed__0, &l_Lean_CollectFVars_State_ofFVarSet___closed__0_once, _init_l_Lean_CollectFVars_State_ofFVarSet___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object* v_fvarSet_7_, lean_object* v_fvarIds_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Lean_CollectFVars_State_ofFVarSet___closed__1, &l_Lean_CollectFVars_State_ofFVarSet___closed__1_once, _init_l_Lean_CollectFVars_State_ofFVarSet___closed__1);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_fvarSet_7_);
lean_ctor_set(v___x_10_, 2, v_fvarIds_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instEmptyCollectionState___closed__1(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = ((lean_object*)(l_Lean_CollectFVars_instEmptyCollectionState___closed__0));
v___x_14_ = lean_box(1);
v___x_15_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_14_, v___x_13_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instEmptyCollectionState(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_CollectFVars_instEmptyCollectionState___closed__1, &l_Lean_CollectFVars_instEmptyCollectionState___closed__1_once, _init_l_Lean_CollectFVars_instEmptyCollectionState___closed__1);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_CollectFVars_instEmptyCollectionState___closed__1, &l_Lean_CollectFVars_instEmptyCollectionState___closed__1_once, _init_l_Lean_CollectFVars_instEmptyCollectionState___closed__1);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object* v_s_18_, lean_object* v_fvarId_19_){
_start:
{
lean_object* v_visited_20_; lean_object* v_fvarSet_21_; lean_object* v_fvarIds_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_31_; 
v_visited_20_ = lean_ctor_get(v_s_18_, 0);
v_fvarSet_21_ = lean_ctor_get(v_s_18_, 1);
v_fvarIds_22_ = lean_ctor_get(v_s_18_, 2);
v_isSharedCheck_31_ = !lean_is_exclusive(v_s_18_);
if (v_isSharedCheck_31_ == 0)
{
v___x_24_ = v_s_18_;
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_fvarIds_22_);
lean_inc(v_fvarSet_21_);
lean_inc(v_visited_20_);
lean_dec(v_s_18_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
lean_inc(v_fvarId_19_);
v___x_26_ = l_Lean_FVarIdSet_insert(v_fvarSet_21_, v_fvarId_19_);
v___x_27_ = lean_array_push(v_fvarIds_22_, v_fvarId_19_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 2, v___x_27_);
lean_ctor_set(v___x_24_, 1, v___x_26_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_visited_20_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg(lean_object* v_k_32_, lean_object* v_t_33_){
_start:
{
if (lean_obj_tag(v_t_33_) == 0)
{
lean_object* v_k_34_; lean_object* v_l_35_; lean_object* v_r_36_; uint8_t v___x_37_; 
v_k_34_ = lean_ctor_get(v_t_33_, 1);
v_l_35_ = lean_ctor_get(v_t_33_, 3);
v_r_36_ = lean_ctor_get(v_t_33_, 4);
v___x_37_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_32_, v_k_34_);
switch(v___x_37_)
{
case 0:
{
v_t_33_ = v_l_35_;
goto _start;
}
case 1:
{
uint8_t v___x_39_; 
v___x_39_ = 1;
return v___x_39_;
}
default: 
{
v_t_33_ = v_r_36_;
goto _start;
}
}
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg___boxed(lean_object* v_k_42_, lean_object* v_t_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg(v_k_42_, v_t_43_);
lean_dec(v_t_43_);
lean_dec(v_k_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
return v_x_46_;
}
else
{
lean_object* v_key_48_; lean_object* v_value_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_76_; 
v_key_48_ = lean_ctor_get(v_x_47_, 0);
v_value_49_ = lean_ctor_get(v_x_47_, 1);
v_tail_50_ = lean_ctor_get(v_x_47_, 2);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_76_ == 0)
{
v___x_52_ = v_x_47_;
v_isShared_53_ = v_isSharedCheck_76_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_value_49_);
lean_inc(v_key_48_);
lean_dec(v_x_47_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_76_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v_fold_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_54_ = lean_array_get_size(v_x_46_);
v___x_55_ = lean_ptr_addr(v_key_48_);
v___x_56_ = ((size_t)3ULL);
v___x_57_ = lean_usize_shift_right(v___x_55_, v___x_56_);
v___x_58_ = lean_usize_to_uint64(v___x_57_);
v___x_59_ = 32ULL;
v___x_60_ = lean_uint64_shift_right(v___x_58_, v___x_59_);
v_fold_61_ = lean_uint64_xor(v___x_58_, v___x_60_);
v___x_62_ = 16ULL;
v___x_63_ = lean_uint64_shift_right(v_fold_61_, v___x_62_);
v___x_64_ = lean_uint64_xor(v_fold_61_, v___x_63_);
v___x_65_ = lean_uint64_to_usize(v___x_64_);
v___x_66_ = lean_usize_of_nat(v___x_54_);
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_sub(v___x_66_, v___x_67_);
v___x_69_ = lean_usize_land(v___x_65_, v___x_68_);
v___x_70_ = lean_array_uget_borrowed(v_x_46_, v___x_69_);
lean_inc(v___x_70_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 2, v___x_70_);
v___x_72_ = v___x_52_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_key_48_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_value_49_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v___x_70_);
v___x_72_ = v_reuseFailAlloc_75_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_array_uset(v_x_46_, v___x_69_, v___x_72_);
v_x_46_ = v___x_73_;
v_x_47_ = v_tail_50_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4___redArg(lean_object* v_i_77_, lean_object* v_source_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_array_get_size(v_source_78_);
v___x_81_ = lean_nat_dec_lt(v_i_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_source_78_);
lean_dec(v_i_77_);
return v_target_79_;
}
else
{
lean_object* v_es_82_; lean_object* v___x_83_; lean_object* v_source_84_; lean_object* v_target_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_es_82_ = lean_array_fget(v_source_78_, v_i_77_);
v___x_83_ = lean_box(0);
v_source_84_ = lean_array_fset(v_source_78_, v_i_77_, v___x_83_);
v_target_85_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(v_target_79_, v_es_82_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_i_77_, v___x_86_);
lean_dec(v_i_77_);
v_i_77_ = v___x_87_;
v_source_78_ = v_source_84_;
v_target_79_ = v_target_85_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2___redArg(lean_object* v_data_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_nbuckets_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_90_ = lean_array_get_size(v_data_89_);
v___x_91_ = lean_unsigned_to_nat(2u);
v_nbuckets_92_ = lean_nat_mul(v___x_90_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_box(0);
v___x_95_ = lean_mk_array(v_nbuckets_92_, v___x_94_);
v___x_96_ = lean_array_propagate_mark(v_data_89_, v___x_95_);
v___x_97_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4___redArg(v___x_93_, v_data_89_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(lean_object* v_a_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
else
{
lean_object* v_key_101_; lean_object* v_tail_102_; size_t v___x_103_; size_t v___x_104_; uint8_t v___x_105_; 
v_key_101_ = lean_ctor_get(v_x_99_, 0);
v_tail_102_ = lean_ctor_get(v_x_99_, 2);
v___x_103_ = lean_ptr_addr(v_key_101_);
v___x_104_ = lean_ptr_addr(v_a_98_);
v___x_105_ = lean_usize_dec_eq(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
v_x_99_ = v_tail_102_;
goto _start;
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(v_a_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec_ref(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object* v_m_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
lean_object* v_size_114_; lean_object* v_buckets_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v_bkt_132_; uint8_t v___x_133_; 
v_size_114_ = lean_ctor_get(v_m_111_, 0);
v_buckets_115_ = lean_ctor_get(v_m_111_, 1);
v___x_116_ = lean_array_get_size(v_buckets_115_);
v___x_117_ = lean_ptr_addr(v_a_112_);
v___x_118_ = ((size_t)3ULL);
v___x_119_ = lean_usize_shift_right(v___x_117_, v___x_118_);
v___x_120_ = lean_usize_to_uint64(v___x_119_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_116_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v_bkt_132_ = lean_array_uget_borrowed(v_buckets_115_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(v_a_112_, v_bkt_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_154_; 
lean_inc_ref(v_buckets_115_);
lean_inc(v_size_114_);
v_isSharedCheck_154_ = !lean_is_exclusive(v_m_111_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_155_ = lean_ctor_get(v_m_111_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_m_111_, 0);
lean_dec(v_unused_156_);
v___x_135_ = v_m_111_;
v_isShared_136_ = v_isSharedCheck_154_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_m_111_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_154_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v_size_x27_138_; lean_object* v___x_139_; lean_object* v_buckets_x27_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v_size_x27_138_ = lean_nat_add(v_size_114_, v___x_137_);
lean_dec(v_size_114_);
lean_inc(v_bkt_132_);
v___x_139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_139_, 0, v_a_112_);
lean_ctor_set(v___x_139_, 1, v_b_113_);
lean_ctor_set(v___x_139_, 2, v_bkt_132_);
v_buckets_x27_140_ = lean_array_uset(v_buckets_115_, v___x_131_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v_size_x27_138_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_div(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_array_get_size(v_buckets_x27_140_);
v___x_146_ = lean_nat_dec_le(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
if (v___x_146_ == 0)
{
lean_object* v_val_147_; lean_object* v___x_149_; 
v_val_147_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2___redArg(v_buckets_x27_140_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_147_);
lean_ctor_set(v___x_135_, 0, v_size_x27_138_);
v___x_149_ = v___x_135_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_val_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_152_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_140_);
lean_ctor_set(v___x_135_, 0, v_size_x27_138_);
v___x_152_ = v___x_135_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_buckets_x27_140_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_dec(v_b_113_);
lean_dec_ref(v_a_112_);
return v_m_111_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object* v_m_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_buckets_159_; lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v_fold_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_buckets_159_ = lean_ctor_get(v_m_157_, 1);
v___x_160_ = lean_array_get_size(v_buckets_159_);
v___x_161_ = lean_ptr_addr(v_a_158_);
v___x_162_ = ((size_t)3ULL);
v___x_163_ = lean_usize_shift_right(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_to_uint64(v___x_163_);
v___x_165_ = 32ULL;
v___x_166_ = lean_uint64_shift_right(v___x_164_, v___x_165_);
v_fold_167_ = lean_uint64_xor(v___x_164_, v___x_166_);
v___x_168_ = 16ULL;
v___x_169_ = lean_uint64_shift_right(v_fold_167_, v___x_168_);
v___x_170_ = lean_uint64_xor(v_fold_167_, v___x_169_);
v___x_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = lean_usize_of_nat(v___x_160_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v___x_172_, v___x_173_);
v___x_175_ = lean_usize_land(v___x_171_, v___x_174_);
v___x_176_ = lean_array_uget_borrowed(v_buckets_159_, v___x_175_);
v___x_177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(v_a_158_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_178_, v_a_179_);
lean_dec_ref(v_a_179_);
lean_dec_ref(v_m_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* v_x_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_d_185_; lean_object* v_b_186_; lean_object* v___y_187_; 
switch(lean_obj_tag(v_x_182_))
{
case 11:
{
lean_object* v_struct_190_; lean_object* v___x_191_; 
v_struct_190_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_struct_190_);
lean_dec_ref_known(v_x_182_, 3);
v___x_191_ = l_Lean_CollectFVars_visit(v_struct_190_, v_a_183_);
return v___x_191_;
}
case 7:
{
lean_object* v_binderType_192_; lean_object* v_body_193_; 
v_binderType_192_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_binderType_192_);
v_body_193_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_body_193_);
lean_dec_ref_known(v_x_182_, 3);
v_d_185_ = v_binderType_192_;
v_b_186_ = v_body_193_;
v___y_187_ = v_a_183_;
goto v___jp_184_;
}
case 6:
{
lean_object* v_binderType_194_; lean_object* v_body_195_; 
v_binderType_194_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_binderType_194_);
v_body_195_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_body_195_);
lean_dec_ref_known(v_x_182_, 3);
v_d_185_ = v_binderType_194_;
v_b_186_ = v_body_195_;
v___y_187_ = v_a_183_;
goto v___jp_184_;
}
case 8:
{
lean_object* v_type_196_; lean_object* v_value_197_; lean_object* v_body_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_type_196_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_type_196_);
v_value_197_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_value_197_);
v_body_198_ = lean_ctor_get(v_x_182_, 3);
lean_inc_ref(v_body_198_);
lean_dec_ref_known(v_x_182_, 4);
v___x_199_ = l_Lean_CollectFVars_visit(v_type_196_, v_a_183_);
v___x_200_ = l_Lean_CollectFVars_visit(v_value_197_, v___x_199_);
v___x_201_ = l_Lean_CollectFVars_visit(v_body_198_, v___x_200_);
return v___x_201_;
}
case 5:
{
lean_object* v_fn_202_; lean_object* v_arg_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_fn_202_ = lean_ctor_get(v_x_182_, 0);
lean_inc_ref(v_fn_202_);
v_arg_203_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_arg_203_);
lean_dec_ref_known(v_x_182_, 2);
v___x_204_ = l_Lean_CollectFVars_visit(v_fn_202_, v_a_183_);
v___x_205_ = l_Lean_CollectFVars_visit(v_arg_203_, v___x_204_);
return v___x_205_;
}
case 10:
{
lean_object* v_expr_206_; lean_object* v___x_207_; 
v_expr_206_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_expr_206_);
lean_dec_ref_known(v_x_182_, 2);
v___x_207_ = l_Lean_CollectFVars_visit(v_expr_206_, v_a_183_);
return v___x_207_;
}
case 1:
{
lean_object* v_fvarId_208_; lean_object* v_fvarSet_209_; uint8_t v___x_210_; 
v_fvarId_208_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_fvarId_208_);
lean_dec_ref_known(v_x_182_, 1);
v_fvarSet_209_ = lean_ctor_get(v_a_183_, 1);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg(v_fvarId_208_, v_fvarSet_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_CollectFVars_State_add(v_a_183_, v_fvarId_208_);
return v___x_211_;
}
else
{
lean_dec(v_fvarId_208_);
return v_a_183_;
}
}
default: 
{
lean_dec_ref(v_x_182_);
return v_a_183_;
}
}
v___jp_184_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = l_Lean_CollectFVars_visit(v_d_185_, v___y_187_);
v___x_189_ = l_Lean_CollectFVars_visit(v_b_186_, v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* v_e_212_, lean_object* v_s_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_Expr_hasFVar(v_e_212_);
if (v___x_214_ == 0)
{
lean_dec_ref(v_e_212_);
return v_s_213_;
}
else
{
lean_object* v_visited_215_; lean_object* v_fvarSet_216_; lean_object* v_fvarIds_217_; uint8_t v___x_218_; 
v_visited_215_ = lean_ctor_get(v_s_213_, 0);
v_fvarSet_216_ = lean_ctor_get(v_s_213_, 1);
v_fvarIds_217_ = lean_ctor_get(v_s_213_, 2);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visited_215_, v_e_212_);
if (v___x_218_ == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
lean_inc_ref(v_fvarIds_217_);
lean_inc(v_fvarSet_216_);
lean_inc_ref(v_visited_215_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_s_213_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_229_ = lean_ctor_get(v_s_213_, 2);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_s_213_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_s_213_, 0);
lean_dec(v_unused_231_);
v___x_220_ = v_s_213_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_s_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = lean_box(0);
lean_inc_ref(v_e_212_);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visited_215_, v_e_212_, v___x_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_fvarSet_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_fvarIds_217_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_CollectFVars_main(v_e_212_, v___x_225_);
return v___x_226_;
}
}
}
else
{
lean_dec_ref(v_e_212_);
return v_s_213_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object* v_00_u03b2_232_, lean_object* v_m_233_, lean_object* v_a_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_233_, v_a_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object* v_00_u03b2_236_, lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(v_00_u03b2_236_, v_m_237_, v_a_238_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_m_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(lean_object* v_00_u03b2_241_, lean_object* v_m_242_, lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_242_, v_a_243_, v_b_244_);
return v___x_245_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3(lean_object* v_00_u03b2_246_, lean_object* v_k_247_, lean_object* v_t_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___redArg(v_k_247_, v_t_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3___boxed(lean_object* v_00_u03b2_250_, lean_object* v_k_251_, lean_object* v_t_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_CollectFVars_main_spec__3(v_00_u03b2_250_, v_k_251_, v_t_252_);
lean_dec(v_t_252_);
lean_dec(v_k_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___redArg(v_a_256_, v_x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_259_, lean_object* v_a_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__0(v_00_u03b2_259_, v_a_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec_ref(v_a_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2(lean_object* v_00_u03b2_264_, lean_object* v_data_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2___redArg(v_data_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_267_, lean_object* v_i_268_, lean_object* v_source_269_, lean_object* v_target_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4___redArg(v_i_268_, v_source_269_, v_target_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__2_spec__4_spec__6___redArg(v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object* v_s_276_, lean_object* v_e_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_CollectFVars_main(v_e_277_, v_s_276_);
return v___x_278_;
}
}
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_instEmptyCollectionState = _init_l_Lean_CollectFVars_instEmptyCollectionState();
lean_mark_persistent(l_Lean_CollectFVars_instEmptyCollectionState);
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
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
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
