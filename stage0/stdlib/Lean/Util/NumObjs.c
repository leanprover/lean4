// Lean compiler output
// Module: Lean.Util.NumObjs
// Imports: public import Lean.Expr public import Lean.Util.PtrSet
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
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_NumObjs_main___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumObjs_main___closed__0;
static lean_once_cell_t l_Lean_Expr_NumObjs_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumObjs_main___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs___boxed(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; size_t v___x_6_; size_t v___x_7_; uint8_t v___x_8_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = lean_ptr_addr(v_key_4_);
v___x_7_ = lean_ptr_addr(v_a_1_);
v___x_8_ = lean_usize_dec_eq(v___x_6_, v___x_7_);
if (v___x_8_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_10_;
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec_ref(v_a_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object* v_m_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_buckets_17_; lean_object* v___x_18_; size_t v___x_19_; uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v_fold_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_buckets_17_ = lean_ctor_get(v_m_15_, 1);
v___x_18_ = lean_array_get_size(v_buckets_17_);
v___x_19_ = lean_ptr_addr(v_a_16_);
v___x_20_ = lean_usize_to_uint64(v___x_19_);
v___x_21_ = 11ULL;
v___x_22_ = lean_uint64_mix_hash(v___x_20_, v___x_21_);
v___x_23_ = 32ULL;
v___x_24_ = lean_uint64_shift_right(v___x_22_, v___x_23_);
v_fold_25_ = lean_uint64_xor(v___x_22_, v___x_24_);
v___x_26_ = 16ULL;
v___x_27_ = lean_uint64_shift_right(v_fold_25_, v___x_26_);
v___x_28_ = lean_uint64_xor(v_fold_25_, v___x_27_);
v___x_29_ = lean_uint64_to_usize(v___x_28_);
v___x_30_ = lean_usize_of_nat(v___x_18_);
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_sub(v___x_30_, v___x_31_);
v___x_33_ = lean_usize_land(v___x_29_, v___x_32_);
v___x_34_ = lean_array_uget_borrowed(v_buckets_17_, v___x_33_);
v___x_35_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_16_, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_15_ = stack[0].m_obj;
lean_object* v_a_16_ = stack[1].m_obj;
uint8_t v_res_36_;
v_res_36_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_15_, v_a_16_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(lean_object* v_m_37_, lean_object* v_a_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_37_, v_a_38_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_m_37_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
return v_x_41_;
}
else
{
lean_object* v_key_43_; lean_object* v_value_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_71_; 
v_key_43_ = lean_ctor_get(v_x_42_, 0);
v_value_44_ = lean_ctor_get(v_x_42_, 1);
v_tail_45_ = lean_ctor_get(v_x_42_, 2);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_71_ == 0)
{
v___x_47_ = v_x_42_;
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_value_44_);
lean_inc(v_key_43_);
lean_dec(v_x_42_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; size_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v_fold_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_49_ = lean_array_get_size(v_x_41_);
v___x_50_ = lean_ptr_addr(v_key_43_);
v___x_51_ = lean_usize_to_uint64(v___x_50_);
v___x_52_ = 11ULL;
v___x_53_ = lean_uint64_mix_hash(v___x_51_, v___x_52_);
v___x_54_ = 32ULL;
v___x_55_ = lean_uint64_shift_right(v___x_53_, v___x_54_);
v_fold_56_ = lean_uint64_xor(v___x_53_, v___x_55_);
v___x_57_ = 16ULL;
v___x_58_ = lean_uint64_shift_right(v_fold_56_, v___x_57_);
v___x_59_ = lean_uint64_xor(v_fold_56_, v___x_58_);
v___x_60_ = lean_uint64_to_usize(v___x_59_);
v___x_61_ = lean_usize_of_nat(v___x_49_);
v___x_62_ = ((size_t)1ULL);
v___x_63_ = lean_usize_sub(v___x_61_, v___x_62_);
v___x_64_ = lean_usize_land(v___x_60_, v___x_63_);
v___x_65_ = lean_array_uget_borrowed(v_x_41_, v___x_64_);
lean_inc(v___x_65_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 2, v___x_65_);
v___x_67_ = v___x_47_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_key_43_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_value_44_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v___x_65_);
v___x_67_ = v_reuseFailAlloc_70_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_array_uset(v_x_41_, v___x_64_, v___x_67_);
v_x_41_ = v___x_68_;
v_x_42_ = v_tail_45_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_72_, lean_object* v_source_73_, lean_object* v_target_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_array_get_size(v_source_73_);
v___x_76_ = lean_nat_dec_lt(v_i_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_dec_ref(v_source_73_);
lean_dec(v_i_72_);
return v_target_74_;
}
else
{
lean_object* v_es_77_; lean_object* v___x_78_; lean_object* v_source_79_; lean_object* v_target_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_es_77_ = lean_array_fget(v_source_73_, v_i_72_);
v___x_78_ = lean_box(0);
v_source_79_ = lean_array_fset(v_source_73_, v_i_72_, v___x_78_);
v_target_80_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_74_, v_es_77_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_i_72_, v___x_81_);
lean_dec(v_i_72_);
v_i_72_ = v___x_82_;
v_source_73_ = v_source_79_;
v_target_74_ = v_target_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(lean_object* v_data_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_nbuckets_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_85_ = lean_array_get_size(v_data_84_);
v___x_86_ = lean_unsigned_to_nat(2u);
v_nbuckets_87_ = lean_nat_mul(v___x_85_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_box(0);
v___x_90_ = lean_mk_array(v_nbuckets_87_, v___x_89_);
v___x_91_ = lean_array_propagate_mark(v_data_84_, v___x_90_);
v___x_92_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v___x_88_, v_data_84_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object* v_m_93_, lean_object* v_a_94_, lean_object* v_b_95_){
_start:
{
lean_object* v_size_96_; lean_object* v_buckets_97_; lean_object* v___x_98_; size_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v_fold_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v_bkt_114_; uint8_t v___x_115_; 
v_size_96_ = lean_ctor_get(v_m_93_, 0);
v_buckets_97_ = lean_ctor_get(v_m_93_, 1);
v___x_98_ = lean_array_get_size(v_buckets_97_);
v___x_99_ = lean_ptr_addr(v_a_94_);
v___x_100_ = lean_usize_to_uint64(v___x_99_);
v___x_101_ = 11ULL;
v___x_102_ = lean_uint64_mix_hash(v___x_100_, v___x_101_);
v___x_103_ = 32ULL;
v___x_104_ = lean_uint64_shift_right(v___x_102_, v___x_103_);
v_fold_105_ = lean_uint64_xor(v___x_102_, v___x_104_);
v___x_106_ = 16ULL;
v___x_107_ = lean_uint64_shift_right(v_fold_105_, v___x_106_);
v___x_108_ = lean_uint64_xor(v_fold_105_, v___x_107_);
v___x_109_ = lean_uint64_to_usize(v___x_108_);
v___x_110_ = lean_usize_of_nat(v___x_98_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_sub(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_land(v___x_109_, v___x_112_);
v_bkt_114_ = lean_array_uget_borrowed(v_buckets_97_, v___x_113_);
v___x_115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_94_, v_bkt_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_buckets_97_);
lean_inc(v_size_96_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_m_93_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; 
v_unused_137_ = lean_ctor_get(v_m_93_, 1);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_m_93_, 0);
lean_dec(v_unused_138_);
v___x_117_ = v_m_93_;
v_isShared_118_ = v_isSharedCheck_136_;
goto v_resetjp_116_;
}
else
{
lean_dec(v_m_93_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_136_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v_size_x27_120_; lean_object* v___x_121_; lean_object* v_buckets_x27_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v_size_x27_120_ = lean_nat_add(v_size_96_, v___x_119_);
lean_dec(v_size_96_);
lean_inc(v_bkt_114_);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v_a_94_);
lean_ctor_set(v___x_121_, 1, v_b_95_);
lean_ctor_set(v___x_121_, 2, v_bkt_114_);
v_buckets_x27_122_ = lean_array_uset(v_buckets_97_, v___x_113_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(4u);
v___x_124_ = lean_nat_mul(v_size_x27_120_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_nat_div(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_array_get_size(v_buckets_x27_122_);
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v_val_129_; lean_object* v___x_131_; 
v_val_129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_buckets_x27_122_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_val_129_);
lean_ctor_set(v___x_117_, 0, v_size_x27_120_);
v___x_131_ = v___x_117_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_val_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_134_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_buckets_x27_122_);
lean_ctor_set(v___x_117_, 0, v_size_x27_120_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_buckets_x27_122_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec(v_b_95_);
lean_dec_ref(v_a_94_);
return v_m_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object* v_e_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_d_142_; lean_object* v_b_143_; lean_object* v___y_144_; lean_object* v_visited_148_; lean_object* v_counter_149_; uint8_t v___x_150_; 
v_visited_148_ = lean_ctor_get(v_a_140_, 0);
v_counter_149_ = lean_ctor_get(v_a_140_, 1);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_visited_148_, v_e_139_);
if (v___x_150_ == 0)
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_183_; 
lean_inc(v_counter_149_);
lean_inc_ref(v_visited_148_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_140_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_184_ = lean_ctor_get(v_a_140_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_a_140_, 0);
lean_dec(v_unused_185_);
v___x_152_ = v_a_140_;
v_isShared_153_ = v_isSharedCheck_183_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_a_140_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_183_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_154_ = lean_box(0);
lean_inc_ref(v_e_139_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_visited_148_, v_e_139_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_counter_149_, v___x_156_);
lean_dec(v_counter_149_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_157_);
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_182_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
switch(lean_obj_tag(v_e_139_))
{
case 7:
{
lean_object* v_binderType_160_; lean_object* v_body_161_; 
v_binderType_160_ = lean_ctor_get(v_e_139_, 1);
lean_inc_ref(v_binderType_160_);
v_body_161_ = lean_ctor_get(v_e_139_, 2);
lean_inc_ref(v_body_161_);
lean_dec_ref_known(v_e_139_, 3);
v_d_142_ = v_binderType_160_;
v_b_143_ = v_body_161_;
v___y_144_ = v___x_159_;
goto v___jp_141_;
}
case 6:
{
lean_object* v_binderType_162_; lean_object* v_body_163_; 
v_binderType_162_ = lean_ctor_get(v_e_139_, 1);
lean_inc_ref(v_binderType_162_);
v_body_163_ = lean_ctor_get(v_e_139_, 2);
lean_inc_ref(v_body_163_);
lean_dec_ref_known(v_e_139_, 3);
v_d_142_ = v_binderType_162_;
v_b_143_ = v_body_163_;
v___y_144_ = v___x_159_;
goto v___jp_141_;
}
case 10:
{
lean_object* v_expr_164_; 
v_expr_164_ = lean_ctor_get(v_e_139_, 1);
lean_inc_ref(v_expr_164_);
lean_dec_ref_known(v_e_139_, 2);
v_e_139_ = v_expr_164_;
v_a_140_ = v___x_159_;
goto _start;
}
case 8:
{
lean_object* v_type_166_; lean_object* v_value_167_; lean_object* v_body_168_; lean_object* v___x_169_; lean_object* v_snd_170_; lean_object* v___x_171_; lean_object* v_snd_172_; 
v_type_166_ = lean_ctor_get(v_e_139_, 1);
lean_inc_ref(v_type_166_);
v_value_167_ = lean_ctor_get(v_e_139_, 2);
lean_inc_ref(v_value_167_);
v_body_168_ = lean_ctor_get(v_e_139_, 3);
lean_inc_ref(v_body_168_);
lean_dec_ref_known(v_e_139_, 4);
v___x_169_ = l_Lean_Expr_NumObjs_visit(v_type_166_, v___x_159_);
v_snd_170_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v___x_169_);
v___x_171_ = l_Lean_Expr_NumObjs_visit(v_value_167_, v_snd_170_);
v_snd_172_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_171_);
v_e_139_ = v_body_168_;
v_a_140_ = v_snd_172_;
goto _start;
}
case 5:
{
lean_object* v_fn_174_; lean_object* v_arg_175_; lean_object* v___x_176_; lean_object* v_snd_177_; 
v_fn_174_ = lean_ctor_get(v_e_139_, 0);
lean_inc_ref(v_fn_174_);
v_arg_175_ = lean_ctor_get(v_e_139_, 1);
lean_inc_ref(v_arg_175_);
lean_dec_ref_known(v_e_139_, 2);
v___x_176_ = l_Lean_Expr_NumObjs_visit(v_fn_174_, v___x_159_);
v_snd_177_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v___x_176_);
v_e_139_ = v_arg_175_;
v_a_140_ = v_snd_177_;
goto _start;
}
case 11:
{
lean_object* v_struct_179_; 
v_struct_179_ = lean_ctor_get(v_e_139_, 2);
lean_inc_ref(v_struct_179_);
lean_dec_ref_known(v_e_139_, 3);
v_e_139_ = v_struct_179_;
v_a_140_ = v___x_159_;
goto _start;
}
default: 
{
lean_object* v___x_181_; 
lean_dec_ref(v_e_139_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_154_);
lean_ctor_set(v___x_181_, 1, v___x_159_);
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref(v_e_139_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_140_);
return v___x_187_;
}
v___jp_141_:
{
lean_object* v___x_145_; lean_object* v_snd_146_; 
v___x_145_ = l_Lean_Expr_NumObjs_visit(v_d_142_, v___y_144_);
v_snd_146_ = lean_ctor_get(v___x_145_, 1);
lean_inc(v_snd_146_);
lean_dec_ref(v___x_145_);
v_e_139_ = v_b_143_;
v_a_140_ = v_snd_146_;
goto _start;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_object* v_00_u03b2_188_, lean_object* v_m_189_, lean_object* v_a_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_189_, v_a_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_189_ = stack[1].m_obj;
lean_object* v_a_190_ = stack[2].m_obj;
uint8_t v_res_192_;
v_res_192_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_box(0), v_m_189_, v_a_190_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(lean_object* v_00_u03b2_193_, lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(v_00_u03b2_193_, v_m_194_, v_a_195_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_m_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1(lean_object* v_00_u03b2_198_, lean_object* v_m_199_, lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_199_, v_a_200_, v_b_201_);
return v___x_202_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_object* v_00_u03b2_203_, lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_204_ = stack[1].m_obj;
lean_object* v_x_205_ = stack[2].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_box(0), v_a_204_, v_x_205_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_208_, lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(v_00_u03b2_208_, v_a_209_, v_x_210_);
lean_dec(v_x_210_);
lean_dec_ref(v_a_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(lean_object* v_00_u03b2_213_, lean_object* v_data_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_data_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_216_, lean_object* v_i_217_, lean_object* v_source_218_, lean_object* v_target_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v_i_217_, v_source_218_, v_target_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_222_, v_x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(64u);
v___x_226_ = l_Lean_mkPtrSet___redArg(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__1(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__0, &l_Lean_Expr_NumObjs_main___closed__0_once, _init_l_Lean_Expr_NumObjs_main___closed__0);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object* v_e_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_snd_233_; lean_object* v_counter_234_; 
v___x_231_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__1, &l_Lean_Expr_NumObjs_main___closed__1_once, _init_l_Lean_Expr_NumObjs_main___closed__1);
v___x_232_ = l_Lean_Expr_NumObjs_visit(v_e_230_, v___x_231_);
v_snd_233_ = lean_ctor_get(v___x_232_, 1);
lean_inc(v_snd_233_);
lean_dec_ref(v___x_232_);
v_counter_234_ = lean_ctor_get(v_snd_233_, 1);
lean_inc(v_counter_234_);
lean_dec(v_snd_233_);
return v_counter_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(lean_object* v_e_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Expr_NumObjs_main(v_e_235_);
return v___x_236_;
}
}
lean_object* l_Lean_Expr_numObjs(lean_object* v_e_237_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = l_Lean_Expr_NumObjs_main(v_e_237_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT void l_Lean_Expr_numObjs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_237_ = stack[0].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_Expr_numObjs(v_e_237_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs___boxed(lean_object* v_e_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Expr_numObjs(v_e_242_);
return v_res_244_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_NumObjs(builtin);
}
#ifdef __cplusplus
}
#endif
