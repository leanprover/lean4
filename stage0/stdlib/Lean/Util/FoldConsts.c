// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: public import Lean.Util.PtrSet public import Lean.Declaration
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
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_NameSet_ofList(lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2;
static lean_once_cell_t l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_getUsedConstants___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_getUsedConstants___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_getUsedConstants___closed__0 = (const lean_object*)&l_Lean_Expr_getUsedConstants___closed__0_value;
static const lean_array_object l_Lean_Expr_getUsedConstants___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_getUsedConstants___closed__1 = (const lean_object*)&l_Lean_Expr_getUsedConstants___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_getUsedConstantsAsSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_getUsedConstantsAsSet___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_getUsedConstantsAsSet___closed__0 = (const lean_object*)&l_Lean_Expr_getUsedConstantsAsSet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec_ref(v_a_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
return v_x_14_;
}
else
{
lean_object* v_key_16_; lean_object* v_value_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_44_; 
v_key_16_ = lean_ctor_get(v_x_15_, 0);
v_value_17_ = lean_ctor_get(v_x_15_, 1);
v_tail_18_ = lean_ctor_get(v_x_15_, 2);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_44_ == 0)
{
v___x_20_ = v_x_15_;
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_value_17_);
lean_inc(v_key_16_);
lean_dec(v_x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; size_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v_fold_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_22_ = lean_array_get_size(v_x_14_);
v___x_23_ = lean_ptr_addr(v_key_16_);
v___x_24_ = lean_usize_to_uint64(v___x_23_);
v___x_25_ = 11ULL;
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
v___x_27_ = 32ULL;
v___x_28_ = lean_uint64_shift_right(v___x_26_, v___x_27_);
v_fold_29_ = lean_uint64_xor(v___x_26_, v___x_28_);
v___x_30_ = 16ULL;
v___x_31_ = lean_uint64_shift_right(v_fold_29_, v___x_30_);
v___x_32_ = lean_uint64_xor(v_fold_29_, v___x_31_);
v___x_33_ = lean_uint64_to_usize(v___x_32_);
v___x_34_ = lean_usize_of_nat(v___x_22_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_sub(v___x_34_, v___x_35_);
v___x_37_ = lean_usize_land(v___x_33_, v___x_36_);
v___x_38_ = lean_array_uget_borrowed(v_x_14_, v___x_37_);
lean_inc(v___x_38_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 2, v___x_38_);
v___x_40_ = v___x_20_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_key_16_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_value_17_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_43_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_array_uset(v_x_14_, v___x_37_, v___x_40_);
v_x_14_ = v___x_41_;
v_x_15_ = v_tail_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_45_, lean_object* v_source_46_, lean_object* v_target_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_array_get_size(v_source_46_);
v___x_49_ = lean_nat_dec_lt(v_i_45_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_source_46_);
lean_dec(v_i_45_);
return v_target_47_;
}
else
{
lean_object* v_es_50_; lean_object* v___x_51_; lean_object* v_source_52_; lean_object* v_target_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_es_50_ = lean_array_fget(v_source_46_, v_i_45_);
v___x_51_ = lean_box(0);
v_source_52_ = lean_array_fset(v_source_46_, v_i_45_, v___x_51_);
v_target_53_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_47_, v_es_50_);
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_add(v_i_45_, v___x_54_);
lean_dec(v_i_45_);
v_i_45_ = v___x_55_;
v_source_46_ = v_source_52_;
v_target_47_ = v_target_53_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(lean_object* v_data_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_nbuckets_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_58_ = lean_array_get_size(v_data_57_);
v___x_59_ = lean_unsigned_to_nat(2u);
v_nbuckets_60_ = lean_nat_mul(v___x_58_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_box(0);
v___x_63_ = lean_mk_array(v_nbuckets_60_, v___x_62_);
v___x_64_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v___x_61_, v_data_57_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object* v_m_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
lean_object* v_size_68_; lean_object* v_buckets_69_; lean_object* v___x_70_; size_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v_fold_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v_bkt_86_; uint8_t v___x_87_; 
v_size_68_ = lean_ctor_get(v_m_65_, 0);
v_buckets_69_ = lean_ctor_get(v_m_65_, 1);
v___x_70_ = lean_array_get_size(v_buckets_69_);
v___x_71_ = lean_ptr_addr(v_a_66_);
v___x_72_ = lean_usize_to_uint64(v___x_71_);
v___x_73_ = 11ULL;
v___x_74_ = lean_uint64_mix_hash(v___x_72_, v___x_73_);
v___x_75_ = 32ULL;
v___x_76_ = lean_uint64_shift_right(v___x_74_, v___x_75_);
v_fold_77_ = lean_uint64_xor(v___x_74_, v___x_76_);
v___x_78_ = 16ULL;
v___x_79_ = lean_uint64_shift_right(v_fold_77_, v___x_78_);
v___x_80_ = lean_uint64_xor(v_fold_77_, v___x_79_);
v___x_81_ = lean_uint64_to_usize(v___x_80_);
v___x_82_ = lean_usize_of_nat(v___x_70_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_sub(v___x_82_, v___x_83_);
v___x_85_ = lean_usize_land(v___x_81_, v___x_84_);
v_bkt_86_ = lean_array_uget_borrowed(v_buckets_69_, v___x_85_);
v___x_87_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_66_, v_bkt_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_108_; 
lean_inc_ref(v_buckets_69_);
lean_inc(v_size_68_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_m_65_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_109_ = lean_ctor_get(v_m_65_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_m_65_, 0);
lean_dec(v_unused_110_);
v___x_89_ = v_m_65_;
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_m_65_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v_size_x27_92_; lean_object* v___x_93_; lean_object* v_buckets_x27_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v_size_x27_92_ = lean_nat_add(v_size_68_, v___x_91_);
lean_dec(v_size_68_);
lean_inc(v_bkt_86_);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v_a_66_);
lean_ctor_set(v___x_93_, 1, v_b_67_);
lean_ctor_set(v___x_93_, 2, v_bkt_86_);
v_buckets_x27_94_ = lean_array_uset(v_buckets_69_, v___x_85_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(4u);
v___x_96_ = lean_nat_mul(v_size_x27_92_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(3u);
v___x_98_ = lean_nat_div(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_array_get_size(v_buckets_x27_94_);
v___x_100_ = lean_nat_dec_le(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
if (v___x_100_ == 0)
{
lean_object* v_val_101_; lean_object* v___x_103_; 
v_val_101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_buckets_x27_94_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_val_101_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_103_ = v___x_89_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_val_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v___x_106_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_buckets_x27_94_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_106_ = v___x_89_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_buckets_x27_94_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_dec(v_b_67_);
lean_dec_ref(v_a_66_);
return v_m_65_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object* v_m_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_buckets_113_; lean_object* v___x_114_; size_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v_fold_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_buckets_113_ = lean_ctor_get(v_m_111_, 1);
v___x_114_ = lean_array_get_size(v_buckets_113_);
v___x_115_ = lean_ptr_addr(v_a_112_);
v___x_116_ = lean_usize_to_uint64(v___x_115_);
v___x_117_ = 11ULL;
v___x_118_ = lean_uint64_mix_hash(v___x_116_, v___x_117_);
v___x_119_ = 32ULL;
v___x_120_ = lean_uint64_shift_right(v___x_118_, v___x_119_);
v_fold_121_ = lean_uint64_xor(v___x_118_, v___x_120_);
v___x_122_ = 16ULL;
v___x_123_ = lean_uint64_shift_right(v_fold_121_, v___x_122_);
v___x_124_ = lean_uint64_xor(v_fold_121_, v___x_123_);
v___x_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = lean_usize_of_nat(v___x_114_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_sub(v___x_126_, v___x_127_);
v___x_129_ = lean_usize_land(v___x_125_, v___x_128_);
v___x_130_ = lean_array_uget_borrowed(v_buckets_113_, v___x_129_);
v___x_131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_112_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_132_, v_a_133_);
lean_dec_ref(v_a_133_);
lean_dec_ref(v_m_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object* v_visitConst_136_, lean_object* v_e_137_, lean_object* v_acc_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_d_141_; lean_object* v_b_142_; lean_object* v___y_143_; lean_object* v_visited_148_; lean_object* v_visitedConsts_149_; uint8_t v___x_150_; 
v_visited_148_ = lean_ctor_get(v_a_139_, 0);
v_visitedConsts_149_ = lean_ctor_get(v_a_139_, 1);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_visited_148_, v_e_137_);
if (v___x_150_ == 0)
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_190_; 
lean_inc_ref(v_visitedConsts_149_);
lean_inc_ref(v_visited_148_);
v_isSharedCheck_190_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_191_ = lean_ctor_get(v_a_139_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_a_139_, 0);
lean_dec(v_unused_192_);
v___x_152_ = v_a_139_;
v_isShared_153_ = v_isSharedCheck_190_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_a_139_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_190_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_box(0);
lean_inc_ref(v_e_137_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_visited_148_, v_e_137_, v___x_154_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_visitedConsts_149_);
v___x_157_ = v_reuseFailAlloc_189_;
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
v_d_141_ = v_binderType_158_;
v_b_142_ = v_body_159_;
v___y_143_ = v___x_157_;
goto v___jp_140_;
}
case 6:
{
lean_object* v_binderType_160_; lean_object* v_body_161_; 
v_binderType_160_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_binderType_160_);
v_body_161_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_body_161_);
lean_dec_ref_known(v_e_137_, 3);
v_d_141_ = v_binderType_160_;
v_b_142_ = v_body_161_;
v___y_143_ = v___x_157_;
goto v___jp_140_;
}
case 10:
{
lean_object* v_expr_162_; 
v_expr_162_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_expr_162_);
lean_dec_ref_known(v_e_137_, 2);
v_e_137_ = v_expr_162_;
v_a_139_ = v___x_157_;
goto _start;
}
case 8:
{
lean_object* v_type_164_; lean_object* v_value_165_; lean_object* v_body_166_; lean_object* v___x_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; 
v_type_164_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_type_164_);
v_value_165_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_value_165_);
v_body_166_ = lean_ctor_get(v_e_137_, 3);
lean_inc_ref(v_body_166_);
lean_dec_ref_known(v_e_137_, 4);
lean_inc_ref_n(v_visitConst_136_, 2);
v___x_167_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_136_, v_type_164_, v_acc_138_, v___x_157_);
v_fst_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v___x_167_);
v___x_170_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_136_, v_value_165_, v_fst_168_, v_snd_169_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_170_);
v_e_137_ = v_body_166_;
v_acc_138_ = v_fst_171_;
v_a_139_ = v_snd_172_;
goto _start;
}
case 5:
{
lean_object* v_fn_174_; lean_object* v_arg_175_; lean_object* v___x_176_; lean_object* v_fst_177_; lean_object* v_snd_178_; 
v_fn_174_ = lean_ctor_get(v_e_137_, 0);
lean_inc_ref(v_fn_174_);
v_arg_175_ = lean_ctor_get(v_e_137_, 1);
lean_inc_ref(v_arg_175_);
lean_dec_ref_known(v_e_137_, 2);
lean_inc_ref(v_visitConst_136_);
v___x_176_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_136_, v_fn_174_, v_acc_138_, v___x_157_);
v_fst_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_fst_177_);
v_snd_178_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_snd_178_);
lean_dec_ref(v___x_176_);
v_e_137_ = v_arg_175_;
v_acc_138_ = v_fst_177_;
v_a_139_ = v_snd_178_;
goto _start;
}
case 11:
{
lean_object* v_typeName_180_; lean_object* v_struct_181_; lean_object* v___x_182_; lean_object* v_fst_183_; lean_object* v_snd_184_; 
v_typeName_180_ = lean_ctor_get(v_e_137_, 0);
lean_inc(v_typeName_180_);
v_struct_181_ = lean_ctor_get(v_e_137_, 2);
lean_inc_ref(v_struct_181_);
lean_dec_ref_known(v_e_137_, 3);
lean_inc_ref(v_visitConst_136_);
v___x_182_ = lean_apply_3(v_visitConst_136_, v_typeName_180_, v_acc_138_, v___x_157_);
v_fst_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_fst_183_);
v_snd_184_ = lean_ctor_get(v___x_182_, 1);
lean_inc(v_snd_184_);
lean_dec_ref(v___x_182_);
v_e_137_ = v_struct_181_;
v_acc_138_ = v_fst_183_;
v_a_139_ = v_snd_184_;
goto _start;
}
case 4:
{
lean_object* v_declName_186_; lean_object* v___x_187_; 
v_declName_186_ = lean_ctor_get(v_e_137_, 0);
lean_inc(v_declName_186_);
lean_dec_ref_known(v_e_137_, 2);
v___x_187_ = lean_apply_3(v_visitConst_136_, v_declName_186_, v_acc_138_, v___x_157_);
return v___x_187_;
}
default: 
{
lean_object* v___x_188_; 
lean_dec_ref(v_e_137_);
lean_dec_ref(v_visitConst_136_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_acc_138_);
lean_ctor_set(v___x_188_, 1, v___x_157_);
return v___x_188_;
}
}
}
}
}
else
{
lean_object* v___x_193_; 
lean_dec_ref(v_e_137_);
lean_dec_ref(v_visitConst_136_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_acc_138_);
lean_ctor_set(v___x_193_, 1, v_a_139_);
return v___x_193_;
}
v___jp_140_:
{
lean_object* v___x_144_; lean_object* v_fst_145_; lean_object* v_snd_146_; 
lean_inc_ref(v_visitConst_136_);
v___x_144_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_136_, v_d_141_, v_acc_138_, v___y_143_);
v_fst_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_145_);
v_snd_146_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_snd_146_);
lean_dec_ref(v___x_144_);
v_e_137_ = v_b_142_;
v_acc_138_ = v_fst_145_;
v_a_139_ = v_snd_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object* v_00_u03b1_194_, lean_object* v_visitConst_195_, lean_object* v_e_196_, lean_object* v_acc_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_195_, v_e_196_, v_acc_197_, v_a_198_);
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object* v_00_u03b2_200_, lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_201_, v_a_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object* v_00_u03b2_204_, lean_object* v_m_205_, lean_object* v_a_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(v_00_u03b2_204_, v_m_205_, v_a_206_);
lean_dec_ref(v_a_206_);
lean_dec_ref(v_m_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_a_211_, lean_object* v_b_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_210_, v_a_211_, v_b_212_);
return v___x_213_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_218_, lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(v_00_u03b2_218_, v_a_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_a_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(lean_object* v_00_u03b2_223_, lean_object* v_data_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_data_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_226_, lean_object* v_i_227_, lean_object* v_source_228_, lean_object* v_target_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v_i_227_, v_source_228_, v_target_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0(lean_object* v_f_235_, lean_object* v_c_236_, lean_object* v_acc_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_visited_239_; lean_object* v_visitedConsts_240_; uint8_t v___x_241_; 
v_visited_239_ = lean_ctor_get(v___y_238_, 0);
v_visitedConsts_240_ = lean_ctor_get(v___y_238_, 1);
v___x_241_ = l_Lean_NameHashSet_contains(v_visitedConsts_240_, v_c_236_);
if (v___x_241_ == 0)
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_251_; 
lean_inc_ref(v_visitedConsts_240_);
lean_inc_ref(v_visited_239_);
v_isSharedCheck_251_ = !lean_is_exclusive(v___y_238_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_252_ = lean_ctor_get(v___y_238_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v___y_238_, 0);
lean_dec(v_unused_253_);
v___x_243_ = v___y_238_;
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
else
{
lean_dec(v___y_238_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_inc(v_c_236_);
v___x_245_ = l_Lean_NameHashSet_insert(v_visitedConsts_240_, v_c_236_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_visited_239_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_250_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_apply_2(v_f_235_, v_c_236_, v_acc_237_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
return v___x_249_;
}
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v_c_236_);
lean_dec(v_f_235_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_acc_237_);
lean_ctor_set(v___x_254_, 1, v___y_238_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object* v_f_255_, lean_object* v_e_256_, lean_object* v_acc_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_visitConst_259_; lean_object* v___x_260_; 
v_visitConst_259_ = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0), 4, 1);
lean_closure_set(v_visitConst_259_, 0, v_f_255_);
v___x_260_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_259_, v_e_256_, v_acc_257_, v_a_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* v_00_u03b1_261_, lean_object* v_f_262_, lean_object* v_e_263_, lean_object* v_acc_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_262_, v_e_263_, v_acc_264_, v_a_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(64u);
v___x_268_ = l_Lean_mkPtrSet___redArg(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_box(0);
v___x_270_ = lean_unsigned_to_nat(16u);
v___x_271_ = lean_mk_array(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2);
v___x_276_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object* v_e_278_, lean_object* v_init_279_, lean_object* v_f_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_fst_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_282_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_280_, v_e_278_, v_init_279_, v___x_281_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_fst_283_);
lean_dec_ref(v___x_282_);
return v_fst_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* v_00_u03b1_284_, lean_object* v_e_285_, lean_object* v_init_286_, lean_object* v_f_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_fst_290_; 
v___x_288_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_289_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_287_, v_e_285_, v_init_286_, v___x_288_);
v_fst_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_fst_290_);
lean_dec_ref(v___x_289_);
return v_fst_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object* v_c_291_, lean_object* v_cs_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_array_push(v_cs_292_, v_c_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* v_e_297_){
_start:
{
lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_fst_302_; 
v___f_298_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__0));
v___x_299_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__1));
v___x_300_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_301_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_298_, v_e_297_, v___x_299_, v___x_300_);
v_fst_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_fst_302_);
lean_dec_ref(v___x_301_);
return v_fst_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object* v_c_303_, lean_object* v_cs_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_NameSet_insert(v_cs_304_, v_c_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* v_e_307_){
_start:
{
lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_fst_312_; 
v___f_308_ = ((lean_object*)(l_Lean_Expr_getUsedConstantsAsSet___closed__0));
v___x_309_ = l_Lean_NameSet_empty;
v___x_310_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_311_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_308_, v_e_307_, v___x_309_, v___x_310_);
v_fst_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_fst_312_);
lean_dec_ref(v___x_311_);
return v_fst_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* v_c_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_ConstantInfo_type(v_c_313_);
v___x_315_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_314_);
v___x_316_ = 1;
lean_inc_ref(v_c_313_);
v___x_317_ = l_Lean_ConstantInfo_value_x3f(v_c_313_, v___x_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
switch(lean_obj_tag(v_c_313_))
{
case 5:
{
lean_object* v_val_318_; lean_object* v_ctors_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_val_318_ = lean_ctor_get(v_c_313_, 0);
lean_inc_ref(v_val_318_);
lean_dec_ref_known(v_c_313_, 1);
v_ctors_319_ = lean_ctor_get(v_val_318_, 4);
lean_inc(v_ctors_319_);
lean_dec_ref(v_val_318_);
v___x_320_ = l_Lean_NameSet_ofList(v_ctors_319_);
lean_dec(v_ctors_319_);
v___x_321_ = l_Lean_NameSet_append(v___x_315_, v___x_320_);
return v___x_321_;
}
case 6:
{
lean_object* v_val_322_; lean_object* v_toConstantVal_323_; lean_object* v_name_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_val_322_ = lean_ctor_get(v_c_313_, 0);
lean_inc_ref(v_val_322_);
lean_dec_ref_known(v_c_313_, 1);
v_toConstantVal_323_ = lean_ctor_get(v_val_322_, 0);
lean_inc_ref(v_toConstantVal_323_);
lean_dec_ref(v_val_322_);
v_name_324_ = lean_ctor_get(v_toConstantVal_323_, 0);
lean_inc(v_name_324_);
lean_dec_ref(v_toConstantVal_323_);
v___x_325_ = l_Lean_NameSet_empty;
v___x_326_ = l_Lean_NameSet_insert(v___x_325_, v_name_324_);
v___x_327_ = l_Lean_NameSet_append(v___x_315_, v___x_326_);
return v___x_327_;
}
case 7:
{
lean_object* v_val_328_; lean_object* v_all_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_val_328_ = lean_ctor_get(v_c_313_, 0);
lean_inc_ref(v_val_328_);
lean_dec_ref_known(v_c_313_, 1);
v_all_329_ = lean_ctor_get(v_val_328_, 1);
lean_inc(v_all_329_);
lean_dec_ref(v_val_328_);
v___x_330_ = l_Lean_NameSet_ofList(v_all_329_);
lean_dec(v_all_329_);
v___x_331_ = l_Lean_NameSet_append(v___x_315_, v___x_330_);
return v___x_331_;
}
default: 
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v_c_313_);
v___x_332_ = l_Lean_NameSet_empty;
v___x_333_ = l_Lean_NameSet_append(v___x_315_, v___x_332_);
return v___x_333_;
}
}
}
else
{
lean_object* v_val_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_c_313_);
v_val_334_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_317_, 1);
v___x_335_ = l_Lean_Expr_getUsedConstantsAsSet(v_val_334_);
v___x_336_ = l_Lean_NameSet_append(v___x_315_, v___x_335_);
return v___x_336_;
}
}
}
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FoldConsts(builtin);
}
#ifdef __cplusplus
}
#endif
