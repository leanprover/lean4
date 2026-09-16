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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec_ref(v_a_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object* v_m_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_buckets_16_; lean_object* v___x_17_; size_t v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v_fold_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_buckets_16_ = lean_ctor_get(v_m_14_, 1);
v___x_17_ = lean_array_get_size(v_buckets_16_);
v___x_18_ = lean_ptr_addr(v_a_15_);
v___x_19_ = lean_usize_to_uint64(v___x_18_);
v___x_20_ = 11ULL;
v___x_21_ = lean_uint64_mix_hash(v___x_19_, v___x_20_);
v___x_22_ = 32ULL;
v___x_23_ = lean_uint64_shift_right(v___x_21_, v___x_22_);
v_fold_24_ = lean_uint64_xor(v___x_21_, v___x_23_);
v___x_25_ = 16ULL;
v___x_26_ = lean_uint64_shift_right(v_fold_24_, v___x_25_);
v___x_27_ = lean_uint64_xor(v_fold_24_, v___x_26_);
v___x_28_ = lean_uint64_to_usize(v___x_27_);
v___x_29_ = lean_usize_of_nat(v___x_17_);
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v___x_29_, v___x_30_);
v___x_32_ = lean_usize_land(v___x_28_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_buckets_16_, v___x_32_);
v___x_34_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_15_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(lean_object* v_m_35_, lean_object* v_a_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_35_, v_a_36_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_m_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
return v_x_39_;
}
else
{
lean_object* v_key_41_; lean_object* v_value_42_; lean_object* v_tail_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_69_; 
v_key_41_ = lean_ctor_get(v_x_40_, 0);
v_value_42_ = lean_ctor_get(v_x_40_, 1);
v_tail_43_ = lean_ctor_get(v_x_40_, 2);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_40_);
if (v_isSharedCheck_69_ == 0)
{
v___x_45_ = v_x_40_;
v_isShared_46_ = v_isSharedCheck_69_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_tail_43_);
lean_inc(v_value_42_);
lean_inc(v_key_41_);
lean_dec(v_x_40_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_69_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; size_t v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v_fold_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_47_ = lean_array_get_size(v_x_39_);
v___x_48_ = lean_ptr_addr(v_key_41_);
v___x_49_ = lean_usize_to_uint64(v___x_48_);
v___x_50_ = 11ULL;
v___x_51_ = lean_uint64_mix_hash(v___x_49_, v___x_50_);
v___x_52_ = 32ULL;
v___x_53_ = lean_uint64_shift_right(v___x_51_, v___x_52_);
v_fold_54_ = lean_uint64_xor(v___x_51_, v___x_53_);
v___x_55_ = 16ULL;
v___x_56_ = lean_uint64_shift_right(v_fold_54_, v___x_55_);
v___x_57_ = lean_uint64_xor(v_fold_54_, v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = lean_usize_of_nat(v___x_47_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_sub(v___x_59_, v___x_60_);
v___x_62_ = lean_usize_land(v___x_58_, v___x_61_);
v___x_63_ = lean_array_uget_borrowed(v_x_39_, v___x_62_);
lean_inc(v___x_63_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 2, v___x_63_);
v___x_65_ = v___x_45_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_key_41_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_value_42_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___x_63_);
v___x_65_ = v_reuseFailAlloc_68_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_array_uset(v_x_39_, v___x_62_, v___x_65_);
v_x_39_ = v___x_66_;
v_x_40_ = v_tail_43_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_70_, lean_object* v_source_71_, lean_object* v_target_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_array_get_size(v_source_71_);
v___x_74_ = lean_nat_dec_lt(v_i_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_dec_ref(v_source_71_);
lean_dec(v_i_70_);
return v_target_72_;
}
else
{
lean_object* v_es_75_; lean_object* v___x_76_; lean_object* v_source_77_; lean_object* v_target_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_es_75_ = lean_array_fget(v_source_71_, v_i_70_);
v___x_76_ = lean_box(0);
v_source_77_ = lean_array_fset(v_source_71_, v_i_70_, v___x_76_);
v_target_78_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_72_, v_es_75_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_i_70_, v___x_79_);
lean_dec(v_i_70_);
v_i_70_ = v___x_80_;
v_source_71_ = v_source_77_;
v_target_72_ = v_target_78_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(lean_object* v_data_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_nbuckets_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_83_ = lean_array_get_size(v_data_82_);
v___x_84_ = lean_unsigned_to_nat(2u);
v_nbuckets_85_ = lean_nat_mul(v___x_83_, v___x_84_);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_box(0);
v___x_88_ = lean_mk_array(v_nbuckets_85_, v___x_87_);
v___x_89_ = lean_array_propagate_mark(v_data_82_, v___x_88_);
v___x_90_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v___x_86_, v_data_82_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object* v_m_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_size_94_; lean_object* v_buckets_95_; lean_object* v___x_96_; size_t v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v_fold_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_bkt_112_; uint8_t v___x_113_; 
v_size_94_ = lean_ctor_get(v_m_91_, 0);
v_buckets_95_ = lean_ctor_get(v_m_91_, 1);
v___x_96_ = lean_array_get_size(v_buckets_95_);
v___x_97_ = lean_ptr_addr(v_a_92_);
v___x_98_ = lean_usize_to_uint64(v___x_97_);
v___x_99_ = 11ULL;
v___x_100_ = lean_uint64_mix_hash(v___x_98_, v___x_99_);
v___x_101_ = 32ULL;
v___x_102_ = lean_uint64_shift_right(v___x_100_, v___x_101_);
v_fold_103_ = lean_uint64_xor(v___x_100_, v___x_102_);
v___x_104_ = 16ULL;
v___x_105_ = lean_uint64_shift_right(v_fold_103_, v___x_104_);
v___x_106_ = lean_uint64_xor(v_fold_103_, v___x_105_);
v___x_107_ = lean_uint64_to_usize(v___x_106_);
v___x_108_ = lean_usize_of_nat(v___x_96_);
v___x_109_ = ((size_t)1ULL);
v___x_110_ = lean_usize_sub(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_land(v___x_107_, v___x_110_);
v_bkt_112_ = lean_array_uget_borrowed(v_buckets_95_, v___x_111_);
v___x_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_92_, v_bkt_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_buckets_95_);
lean_inc(v_size_94_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_m_91_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_m_91_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_m_91_, 0);
lean_dec(v_unused_136_);
v___x_115_ = v_m_91_;
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
else
{
lean_dec(v_m_91_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_134_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v_size_x27_118_; lean_object* v___x_119_; lean_object* v_buckets_x27_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v_size_x27_118_ = lean_nat_add(v_size_94_, v___x_117_);
lean_dec(v_size_94_);
lean_inc(v_bkt_112_);
v___x_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_119_, 0, v_a_92_);
lean_ctor_set(v___x_119_, 1, v_b_93_);
lean_ctor_set(v___x_119_, 2, v_bkt_112_);
v_buckets_x27_120_ = lean_array_uset(v_buckets_95_, v___x_111_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_mul(v_size_x27_118_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(3u);
v___x_124_ = lean_nat_div(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_array_get_size(v_buckets_x27_120_);
v___x_126_ = lean_nat_dec_le(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v_val_127_; lean_object* v___x_129_; 
v_val_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_buckets_x27_120_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_val_127_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_129_ = v___x_115_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_val_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_132_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_buckets_x27_120_);
lean_ctor_set(v___x_115_, 0, v_size_x27_118_);
v___x_132_ = v___x_115_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_buckets_x27_120_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_dec(v_b_93_);
lean_dec_ref(v_a_92_);
return v_m_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_visit(lean_object* v_e_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_d_140_; lean_object* v_b_141_; lean_object* v___y_142_; lean_object* v_visited_146_; lean_object* v_counter_147_; uint8_t v___x_148_; 
v_visited_146_ = lean_ctor_get(v_a_138_, 0);
v_counter_147_ = lean_ctor_get(v_a_138_, 1);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_visited_146_, v_e_137_);
if (v___x_148_ == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_181_; 
lean_inc(v_counter_147_);
lean_inc_ref(v_visited_146_);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_138_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_182_ = lean_ctor_get(v_a_138_, 1);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_a_138_, 0);
lean_dec(v_unused_183_);
v___x_150_ = v_a_138_;
v_isShared_151_ = v_isSharedCheck_181_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_a_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_181_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_152_ = lean_box(0);
lean_inc_ref(v_e_137_);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_visited_146_, v_e_137_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_counter_147_, v___x_154_);
lean_dec(v_counter_147_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_155_);
lean_ctor_set(v___x_150_, 0, v___x_153_);
v___x_157_ = v___x_150_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_180_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
switch(lean_obj_tag(v_e_137_))
{
case 7:
{
lean_object* v_binderType_158_; lean_object* v_body_159_; 
v_binderType_158_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_binderType_158_);
v_body_159_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_body_159_);
lean_dec_ref_known(v_e_137_, 3);
v_d_140_ = v_binderType_158_;
v_b_141_ = v_body_159_;
v___y_142_ = v___x_157_;
goto v___jp_139_;
}
case 6:
{
lean_object* v_binderType_160_; lean_object* v_body_161_; 
v_binderType_160_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_binderType_160_);
v_body_161_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_body_161_);
lean_dec_ref_known(v_e_137_, 3);
v_d_140_ = v_binderType_160_;
v_b_141_ = v_body_161_;
v___y_142_ = v___x_157_;
goto v___jp_139_;
}
case 10:
{
lean_object* v_expr_162_; 
v_expr_162_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_expr_162_);
lean_dec_ref_known(v_e_137_, 2);
v_e_137_ = v_expr_162_;
v_a_138_ = v___x_157_;
goto _start;
}
case 8:
{
lean_object* v_type_164_; lean_object* v_value_165_; lean_object* v_body_166_; lean_object* v___x_167_; lean_object* v_snd_168_; lean_object* v___x_169_; lean_object* v_snd_170_; 
v_type_164_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_type_164_);
v_value_165_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_value_165_);
v_body_166_ = lean_ctor_get(v_e_137_, 3);
lean_inc_ref(v_body_166_);
lean_dec_ref_known(v_e_137_, 4);
v___x_167_ = l_Lean_Expr_NumObjs_visit(v_type_164_, v___x_157_);
v_snd_168_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_snd_168_);
lean_dec_ref(v___x_167_);
v___x_169_ = l_Lean_Expr_NumObjs_visit(v_value_165_, v_snd_168_);
v_snd_170_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v___x_169_);
v_e_137_ = v_body_166_;
v_a_138_ = v_snd_170_;
goto _start;
}
case 5:
{
lean_object* v_fn_172_; lean_object* v_arg_173_; lean_object* v___x_174_; lean_object* v_snd_175_; 
v_fn_172_ = lean_ctor_get(v_e_137_, 0);
lean_inc_ref(v_fn_172_);
v_arg_173_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_arg_173_);
lean_dec_ref_known(v_e_137_, 2);
v___x_174_ = l_Lean_Expr_NumObjs_visit(v_fn_172_, v___x_157_);
v_snd_175_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_snd_175_);
lean_dec_ref(v___x_174_);
v_e_137_ = v_arg_173_;
v_a_138_ = v_snd_175_;
goto _start;
}
case 11:
{
lean_object* v_struct_177_; 
v_struct_177_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_struct_177_);
lean_dec_ref_known(v_e_137_, 3);
v_e_137_ = v_struct_177_;
v_a_138_ = v___x_157_;
goto _start;
}
default: 
{
lean_object* v___x_179_; 
lean_dec_ref(v_e_137_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_152_);
lean_ctor_set(v___x_179_, 1, v___x_157_);
return v___x_179_;
}
}
}
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec_ref(v_e_137_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_138_);
return v___x_185_;
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v_snd_144_; 
v___x_143_ = l_Lean_Expr_NumObjs_visit(v_d_140_, v___y_142_);
v_snd_144_ = lean_ctor_get(v___x_143_, 1);
lean_inc(v_snd_144_);
lean_dec_ref(v___x_143_);
v_e_137_ = v_b_141_;
v_a_138_ = v_snd_144_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_187_, v_a_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(lean_object* v_00_u03b2_190_, lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(v_00_u03b2_190_, v_m_191_, v_a_192_);
lean_dec_ref(v_a_192_);
lean_dec_ref(v_m_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1(lean_object* v_00_u03b2_195_, lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_196_, v_a_197_, v_b_198_);
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_201_, v_x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_204_, lean_object* v_a_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(v_00_u03b2_204_, v_a_205_, v_x_206_);
lean_dec(v_x_206_);
lean_dec_ref(v_a_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(lean_object* v_00_u03b2_209_, lean_object* v_data_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_data_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_212_, lean_object* v_i_213_, lean_object* v_source_214_, lean_object* v_target_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v_i_213_, v_source_214_, v_target_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_218_, v_x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(64u);
v___x_222_ = l_Lean_mkPtrSet___redArg(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Expr_NumObjs_main___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__0, &l_Lean_Expr_NumObjs_main___closed__0_once, _init_l_Lean_Expr_NumObjs_main___closed__0);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumObjs_main(lean_object* v_e_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_snd_229_; lean_object* v_counter_230_; 
v___x_227_ = lean_obj_once(&l_Lean_Expr_NumObjs_main___closed__1, &l_Lean_Expr_NumObjs_main___closed__1_once, _init_l_Lean_Expr_NumObjs_main___closed__1);
v___x_228_ = l_Lean_Expr_NumObjs_visit(v_e_226_, v___x_227_);
v_snd_229_ = lean_ctor_get(v___x_228_, 1);
lean_inc(v_snd_229_);
lean_dec_ref(v___x_228_);
v_counter_230_ = lean_ctor_get(v_snd_229_, 1);
lean_inc(v_counter_230_);
lean_dec(v_snd_229_);
return v_counter_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(lean_object* v_e_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Expr_NumObjs_main(v_e_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs(lean_object* v_e_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = l_Lean_Expr_NumObjs_main(v_e_233_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numObjs___boxed(lean_object* v_e_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Expr_numObjs(v_e_237_);
return v_res_239_;
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
