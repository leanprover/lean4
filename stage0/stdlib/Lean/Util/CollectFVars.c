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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object* v_a_29_, lean_object* v_x_30_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[0].m_obj;
lean_object* v_x_30_ = stack[1].m_obj;
uint8_t v_res_36_;
v_res_36_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_29_, v_x_30_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_a_37_, lean_object* v_x_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_37_, v_x_38_);
lean_dec(v_x_38_);
lean_dec_ref(v_a_37_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
return v_x_41_;
}
else
{
lean_object* v_key_43_; lean_object* v_value_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_68_; 
v_key_43_ = lean_ctor_get(v_x_42_, 0);
v_value_44_ = lean_ctor_get(v_x_42_, 1);
v_tail_45_ = lean_ctor_get(v_x_42_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_68_ == 0)
{
v___x_47_ = v_x_42_;
v_isShared_48_ = v_isSharedCheck_68_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_value_44_);
lean_inc(v_key_43_);
lean_dec(v_x_42_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_68_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v_fold_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; size_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_49_ = lean_array_get_size(v_x_41_);
v___x_50_ = l_Lean_Expr_hash(v_key_43_);
v___x_51_ = 32ULL;
v___x_52_ = lean_uint64_shift_right(v___x_50_, v___x_51_);
v_fold_53_ = lean_uint64_xor(v___x_50_, v___x_52_);
v___x_54_ = 16ULL;
v___x_55_ = lean_uint64_shift_right(v_fold_53_, v___x_54_);
v___x_56_ = lean_uint64_xor(v_fold_53_, v___x_55_);
v___x_57_ = lean_uint64_to_usize(v___x_56_);
v___x_58_ = lean_usize_of_nat(v___x_49_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_sub(v___x_58_, v___x_59_);
v___x_61_ = lean_usize_land(v___x_57_, v___x_60_);
v___x_62_ = lean_array_uget_borrowed(v_x_41_, v___x_61_);
lean_inc(v___x_62_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 2, v___x_62_);
v___x_64_ = v___x_47_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_key_43_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_value_44_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v___x_62_);
v___x_64_ = v_reuseFailAlloc_67_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_array_uset(v_x_41_, v___x_61_, v___x_64_);
v_x_41_ = v___x_65_;
v_x_42_ = v_tail_45_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(lean_object* v_i_69_, lean_object* v_source_70_, lean_object* v_target_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_array_get_size(v_source_70_);
v___x_73_ = lean_nat_dec_lt(v_i_69_, v___x_72_);
if (v___x_73_ == 0)
{
lean_dec_ref(v_source_70_);
lean_dec(v_i_69_);
return v_target_71_;
}
else
{
lean_object* v_es_74_; lean_object* v___x_75_; lean_object* v_source_76_; lean_object* v_target_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_es_74_ = lean_array_fget(v_source_70_, v_i_69_);
v___x_75_ = lean_box(0);
v_source_76_ = lean_array_fset(v_source_70_, v_i_69_, v___x_75_);
v_target_77_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_target_71_, v_es_74_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_i_69_, v___x_78_);
lean_dec(v_i_69_);
v_i_69_ = v___x_79_;
v_source_70_ = v_source_76_;
v_target_71_ = v_target_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(lean_object* v_data_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_nbuckets_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_82_ = lean_array_get_size(v_data_81_);
v___x_83_ = lean_unsigned_to_nat(2u);
v_nbuckets_84_ = lean_nat_mul(v___x_82_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_box(0);
v___x_87_ = lean_mk_array(v_nbuckets_84_, v___x_86_);
v___x_88_ = lean_array_propagate_mark(v_data_81_, v___x_87_);
v___x_89_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v___x_85_, v_data_81_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object* v_m_90_, lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
lean_object* v_size_93_; lean_object* v_buckets_94_; lean_object* v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v_fold_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; lean_object* v_bkt_108_; uint8_t v___x_109_; 
v_size_93_ = lean_ctor_get(v_m_90_, 0);
v_buckets_94_ = lean_ctor_get(v_m_90_, 1);
v___x_95_ = lean_array_get_size(v_buckets_94_);
v___x_96_ = l_Lean_Expr_hash(v_a_91_);
v___x_97_ = 32ULL;
v___x_98_ = lean_uint64_shift_right(v___x_96_, v___x_97_);
v_fold_99_ = lean_uint64_xor(v___x_96_, v___x_98_);
v___x_100_ = 16ULL;
v___x_101_ = lean_uint64_shift_right(v_fold_99_, v___x_100_);
v___x_102_ = lean_uint64_xor(v_fold_99_, v___x_101_);
v___x_103_ = lean_uint64_to_usize(v___x_102_);
v___x_104_ = lean_usize_of_nat(v___x_95_);
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_sub(v___x_104_, v___x_105_);
v___x_107_ = lean_usize_land(v___x_103_, v___x_106_);
v_bkt_108_ = lean_array_uget_borrowed(v_buckets_94_, v___x_107_);
v___x_109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_91_, v_bkt_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_130_; 
lean_inc_ref(v_buckets_94_);
lean_inc(v_size_93_);
v_isSharedCheck_130_ = !lean_is_exclusive(v_m_90_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_131_ = lean_ctor_get(v_m_90_, 1);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v_m_90_, 0);
lean_dec(v_unused_132_);
v___x_111_ = v_m_90_;
v_isShared_112_ = v_isSharedCheck_130_;
goto v_resetjp_110_;
}
else
{
lean_dec(v_m_90_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_130_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v_size_x27_114_; lean_object* v___x_115_; lean_object* v_buckets_x27_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v_size_x27_114_ = lean_nat_add(v_size_93_, v___x_113_);
lean_dec(v_size_93_);
lean_inc(v_bkt_108_);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v_a_91_);
lean_ctor_set(v___x_115_, 1, v_b_92_);
lean_ctor_set(v___x_115_, 2, v_bkt_108_);
v_buckets_x27_116_ = lean_array_uset(v_buckets_94_, v___x_107_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(4u);
v___x_118_ = lean_nat_mul(v_size_x27_114_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = lean_nat_div(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_array_get_size(v_buckets_x27_116_);
v___x_122_ = lean_nat_dec_le(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v_val_123_; lean_object* v___x_125_; 
v_val_123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_buckets_x27_116_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v_val_123_);
lean_ctor_set(v___x_111_, 0, v_size_x27_114_);
v___x_125_ = v___x_111_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_size_x27_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_val_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v___x_128_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v_buckets_x27_116_);
lean_ctor_set(v___x_111_, 0, v_size_x27_114_);
v___x_128_ = v___x_111_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_x27_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_buckets_x27_116_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_dec(v_b_92_);
lean_dec_ref(v_a_91_);
return v_m_90_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_buckets_135_; lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_buckets_135_ = lean_ctor_get(v_m_133_, 1);
v___x_136_ = lean_array_get_size(v_buckets_135_);
v___x_137_ = l_Lean_Expr_hash(v_a_134_);
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___x_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___x_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_136_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v___x_149_ = lean_array_uget_borrowed(v_buckets_135_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_134_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_133_ = stack[0].m_obj;
lean_object* v_a_134_ = stack[1].m_obj;
uint8_t v_res_151_;
v_res_151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_133_, v_a_134_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object* v_m_152_, lean_object* v_a_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_152_, v_a_153_);
lean_dec_ref(v_a_153_);
lean_dec_ref(v_m_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* v_x_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_d_159_; lean_object* v_b_160_; lean_object* v___y_161_; 
switch(lean_obj_tag(v_x_156_))
{
case 11:
{
lean_object* v_struct_164_; lean_object* v___x_165_; 
v_struct_164_ = lean_ctor_get(v_x_156_, 2);
lean_inc_ref(v_struct_164_);
lean_dec_ref_known(v_x_156_, 3);
v___x_165_ = l_Lean_CollectFVars_visit(v_struct_164_, v_a_157_);
return v___x_165_;
}
case 7:
{
lean_object* v_binderType_166_; lean_object* v_body_167_; 
v_binderType_166_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_binderType_166_);
v_body_167_ = lean_ctor_get(v_x_156_, 2);
lean_inc_ref(v_body_167_);
lean_dec_ref_known(v_x_156_, 3);
v_d_159_ = v_binderType_166_;
v_b_160_ = v_body_167_;
v___y_161_ = v_a_157_;
goto v___jp_158_;
}
case 6:
{
lean_object* v_binderType_168_; lean_object* v_body_169_; 
v_binderType_168_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_binderType_168_);
v_body_169_ = lean_ctor_get(v_x_156_, 2);
lean_inc_ref(v_body_169_);
lean_dec_ref_known(v_x_156_, 3);
v_d_159_ = v_binderType_168_;
v_b_160_ = v_body_169_;
v___y_161_ = v_a_157_;
goto v___jp_158_;
}
case 8:
{
lean_object* v_type_170_; lean_object* v_value_171_; lean_object* v_body_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_type_170_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_type_170_);
v_value_171_ = lean_ctor_get(v_x_156_, 2);
lean_inc_ref(v_value_171_);
v_body_172_ = lean_ctor_get(v_x_156_, 3);
lean_inc_ref(v_body_172_);
lean_dec_ref_known(v_x_156_, 4);
v___x_173_ = l_Lean_CollectFVars_visit(v_type_170_, v_a_157_);
v___x_174_ = l_Lean_CollectFVars_visit(v_value_171_, v___x_173_);
v___x_175_ = l_Lean_CollectFVars_visit(v_body_172_, v___x_174_);
return v___x_175_;
}
case 5:
{
lean_object* v_fn_176_; lean_object* v_arg_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fn_176_ = lean_ctor_get(v_x_156_, 0);
lean_inc_ref(v_fn_176_);
v_arg_177_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_arg_177_);
lean_dec_ref_known(v_x_156_, 2);
v___x_178_ = l_Lean_CollectFVars_visit(v_fn_176_, v_a_157_);
v___x_179_ = l_Lean_CollectFVars_visit(v_arg_177_, v___x_178_);
return v___x_179_;
}
case 10:
{
lean_object* v_expr_180_; lean_object* v___x_181_; 
v_expr_180_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_expr_180_);
lean_dec_ref_known(v_x_156_, 2);
v___x_181_ = l_Lean_CollectFVars_visit(v_expr_180_, v_a_157_);
return v___x_181_;
}
case 1:
{
lean_object* v_fvarId_182_; lean_object* v___x_183_; 
v_fvarId_182_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_fvarId_182_);
lean_dec_ref_known(v_x_156_, 1);
v___x_183_ = l_Lean_CollectFVars_State_add(v_a_157_, v_fvarId_182_);
return v___x_183_;
}
default: 
{
lean_dec_ref(v_x_156_);
return v_a_157_;
}
}
v___jp_158_:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Lean_CollectFVars_visit(v_d_159_, v___y_161_);
v___x_163_ = l_Lean_CollectFVars_visit(v_b_160_, v___x_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* v_e_184_, lean_object* v_s_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Expr_hasFVar(v_e_184_);
if (v___x_186_ == 0)
{
lean_dec_ref(v_e_184_);
return v_s_185_;
}
else
{
lean_object* v_visitedExpr_187_; lean_object* v_fvarSet_188_; lean_object* v_fvarIds_189_; uint8_t v___x_190_; 
v_visitedExpr_187_ = lean_ctor_get(v_s_185_, 0);
v_fvarSet_188_ = lean_ctor_get(v_s_185_, 1);
v_fvarIds_189_ = lean_ctor_get(v_s_185_, 2);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visitedExpr_187_, v_e_184_);
if (v___x_190_ == 0)
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
lean_inc_ref(v_fvarIds_189_);
lean_inc(v_fvarSet_188_);
lean_inc_ref(v_visitedExpr_187_);
v_isSharedCheck_200_ = !lean_is_exclusive(v_s_185_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; lean_object* v_unused_203_; 
v_unused_201_ = lean_ctor_get(v_s_185_, 2);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_s_185_, 1);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_s_185_, 0);
lean_dec(v_unused_203_);
v___x_192_ = v_s_185_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_dec(v_s_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = lean_box(0);
lean_inc_ref(v_e_184_);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visitedExpr_187_, v_e_184_, v___x_194_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_fvarSet_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_fvarIds_189_);
v___x_197_ = v_reuseFailAlloc_199_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_CollectFVars_main(v_e_184_, v___x_197_);
return v___x_198_;
}
}
}
else
{
lean_dec_ref(v_e_184_);
return v_s_185_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object* v_00_u03b2_204_, lean_object* v_m_205_, lean_object* v_a_206_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_205_, v_a_206_);
return v___x_207_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_205_ = stack[1].m_obj;
lean_object* v_a_206_ = stack[2].m_obj;
uint8_t v_res_208_;
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_box(0), v_m_205_, v_a_206_);
stack->m_num = v_res_208_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_a_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(v_00_u03b2_209_, v_m_210_, v_a_211_);
lean_dec_ref(v_a_211_);
lean_dec_ref(v_m_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(lean_object* v_00_u03b2_214_, lean_object* v_m_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_215_, v_a_216_, v_b_217_);
return v___x_218_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_219_, lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_220_ = stack[1].m_obj;
lean_object* v_x_221_ = stack[2].m_obj;
uint8_t v_res_223_;
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_box(0), v_a_220_, v_x_221_);
stack->m_num = v_res_223_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_224_, lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(v_00_u03b2_224_, v_a_225_, v_x_226_);
lean_dec(v_x_226_);
lean_dec_ref(v_a_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_229_, lean_object* v_data_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_data_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_232_, lean_object* v_i_233_, lean_object* v_source_234_, lean_object* v_target_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v_i_233_, v_source_234_, v_target_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_x_238_, v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object* v_s_241_, lean_object* v_e_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_CollectFVars_main(v_e_242_, v_s_241_);
return v___x_243_;
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
