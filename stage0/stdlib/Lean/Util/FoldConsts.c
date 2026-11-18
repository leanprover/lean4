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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_nbuckets_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_58_ = lean_array_get_size(v_data_57_);
v___x_59_ = lean_unsigned_to_nat(2u);
v_nbuckets_60_ = lean_nat_mul(v___x_58_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_box(0);
v___x_63_ = lean_mk_array(v_nbuckets_60_, v___x_62_);
v___x_64_ = lean_array_propagate_mark(v_data_57_, v___x_63_);
v___x_65_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v___x_61_, v_data_57_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object* v_m_66_, lean_object* v_a_67_, lean_object* v_b_68_){
_start:
{
lean_object* v_size_69_; lean_object* v_buckets_70_; lean_object* v___x_71_; size_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v_bkt_87_; uint8_t v___x_88_; 
v_size_69_ = lean_ctor_get(v_m_66_, 0);
v_buckets_70_ = lean_ctor_get(v_m_66_, 1);
v___x_71_ = lean_array_get_size(v_buckets_70_);
v___x_72_ = lean_ptr_addr(v_a_67_);
v___x_73_ = lean_usize_to_uint64(v___x_72_);
v___x_74_ = 11ULL;
v___x_75_ = lean_uint64_mix_hash(v___x_73_, v___x_74_);
v___x_76_ = 32ULL;
v___x_77_ = lean_uint64_shift_right(v___x_75_, v___x_76_);
v_fold_78_ = lean_uint64_xor(v___x_75_, v___x_77_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_71_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v_bkt_87_ = lean_array_uget_borrowed(v_buckets_70_, v___x_86_);
v___x_88_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_67_, v_bkt_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_109_; 
lean_inc_ref(v_buckets_70_);
lean_inc(v_size_69_);
v_isSharedCheck_109_ = !lean_is_exclusive(v_m_66_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_110_ = lean_ctor_get(v_m_66_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_m_66_, 0);
lean_dec(v_unused_111_);
v___x_90_ = v_m_66_;
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_m_66_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v_size_x27_93_; lean_object* v___x_94_; lean_object* v_buckets_x27_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v_size_x27_93_ = lean_nat_add(v_size_69_, v___x_92_);
lean_dec(v_size_69_);
lean_inc(v_bkt_87_);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v_a_67_);
lean_ctor_set(v___x_94_, 1, v_b_68_);
lean_ctor_set(v___x_94_, 2, v_bkt_87_);
v_buckets_x27_95_ = lean_array_uset(v_buckets_70_, v___x_86_, v___x_94_);
v___x_96_ = lean_unsigned_to_nat(4u);
v___x_97_ = lean_nat_mul(v_size_x27_93_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = lean_nat_div(v___x_97_, v___x_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_array_get_size(v_buckets_x27_95_);
v___x_101_ = lean_nat_dec_le(v___x_99_, v___x_100_);
lean_dec(v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v_val_102_; lean_object* v___x_104_; 
v_val_102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_buckets_x27_95_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_val_102_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_104_ = v___x_90_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_val_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_buckets_x27_95_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_107_ = v___x_90_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_buckets_x27_95_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_dec(v_b_68_);
lean_dec_ref(v_a_67_);
return v_m_66_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object* v_m_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_buckets_114_; lean_object* v___x_115_; size_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_buckets_114_ = lean_ctor_get(v_m_112_, 1);
v___x_115_ = lean_array_get_size(v_buckets_114_);
v___x_116_ = lean_ptr_addr(v_a_113_);
v___x_117_ = lean_usize_to_uint64(v___x_116_);
v___x_118_ = 11ULL;
v___x_119_ = lean_uint64_mix_hash(v___x_117_, v___x_118_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_115_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_array_uget_borrowed(v_buckets_114_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_113_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_133_, v_a_134_);
lean_dec_ref(v_a_134_);
lean_dec_ref(v_m_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object* v_visitConst_137_, lean_object* v_e_138_, lean_object* v_acc_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_d_142_; lean_object* v_b_143_; lean_object* v___y_144_; lean_object* v_visited_149_; lean_object* v_visitedConsts_150_; uint8_t v___x_151_; 
v_visited_149_ = lean_ctor_get(v_a_140_, 0);
v_visitedConsts_150_ = lean_ctor_get(v_a_140_, 1);
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_visited_149_, v_e_138_);
if (v___x_151_ == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_191_; 
lean_inc_ref(v_visitedConsts_150_);
lean_inc_ref(v_visited_149_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_a_140_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; 
v_unused_192_ = lean_ctor_get(v_a_140_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_a_140_, 0);
lean_dec(v_unused_193_);
v___x_153_ = v_a_140_;
v_isShared_154_ = v_isSharedCheck_191_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_a_140_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_191_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_box(0);
lean_inc_ref(v_e_138_);
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_visited_149_, v_e_138_, v___x_155_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_visitedConsts_150_);
v___x_158_ = v_reuseFailAlloc_190_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
switch(lean_obj_tag(v_e_138_))
{
case 7:
{
lean_object* v_binderType_159_; lean_object* v_body_160_; 
v_binderType_159_ = lean_ctor_get(v_e_138_, 1);
lean_inc_ref(v_binderType_159_);
v_body_160_ = lean_ctor_get(v_e_138_, 2);
lean_inc_ref(v_body_160_);
lean_dec_ref_known(v_e_138_, 3);
v_d_142_ = v_binderType_159_;
v_b_143_ = v_body_160_;
v___y_144_ = v___x_158_;
goto v___jp_141_;
}
case 6:
{
lean_object* v_binderType_161_; lean_object* v_body_162_; 
v_binderType_161_ = lean_ctor_get(v_e_138_, 1);
lean_inc_ref(v_binderType_161_);
v_body_162_ = lean_ctor_get(v_e_138_, 2);
lean_inc_ref(v_body_162_);
lean_dec_ref_known(v_e_138_, 3);
v_d_142_ = v_binderType_161_;
v_b_143_ = v_body_162_;
v___y_144_ = v___x_158_;
goto v___jp_141_;
}
case 10:
{
lean_object* v_expr_163_; 
v_expr_163_ = lean_ctor_get(v_e_138_, 1);
lean_inc_ref(v_expr_163_);
lean_dec_ref_known(v_e_138_, 2);
v_e_138_ = v_expr_163_;
v_a_140_ = v___x_158_;
goto _start;
}
case 8:
{
lean_object* v_type_165_; lean_object* v_value_166_; lean_object* v_body_167_; lean_object* v___x_168_; lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; 
v_type_165_ = lean_ctor_get(v_e_138_, 1);
lean_inc_ref(v_type_165_);
v_value_166_ = lean_ctor_get(v_e_138_, 2);
lean_inc_ref(v_value_166_);
v_body_167_ = lean_ctor_get(v_e_138_, 3);
lean_inc_ref(v_body_167_);
lean_dec_ref_known(v_e_138_, 4);
lean_inc_ref_n(v_visitConst_137_, 2);
v___x_168_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_137_, v_type_165_, v_acc_139_, v___x_158_);
v_fst_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_fst_169_);
v_snd_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v___x_168_);
v___x_171_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_137_, v_value_166_, v_fst_169_, v_snd_170_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_fst_172_);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_snd_173_);
lean_dec_ref(v___x_171_);
v_e_138_ = v_body_167_;
v_acc_139_ = v_fst_172_;
v_a_140_ = v_snd_173_;
goto _start;
}
case 5:
{
lean_object* v_fn_175_; lean_object* v_arg_176_; lean_object* v___x_177_; lean_object* v_fst_178_; lean_object* v_snd_179_; 
v_fn_175_ = lean_ctor_get(v_e_138_, 0);
lean_inc_ref(v_fn_175_);
v_arg_176_ = lean_ctor_get(v_e_138_, 1);
lean_inc_ref(v_arg_176_);
lean_dec_ref_known(v_e_138_, 2);
lean_inc_ref(v_visitConst_137_);
v___x_177_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_137_, v_fn_175_, v_acc_139_, v___x_158_);
v_fst_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v___x_177_, 1);
lean_inc(v_snd_179_);
lean_dec_ref(v___x_177_);
v_e_138_ = v_arg_176_;
v_acc_139_ = v_fst_178_;
v_a_140_ = v_snd_179_;
goto _start;
}
case 11:
{
lean_object* v_typeName_181_; lean_object* v_struct_182_; lean_object* v___x_183_; lean_object* v_fst_184_; lean_object* v_snd_185_; 
v_typeName_181_ = lean_ctor_get(v_e_138_, 0);
lean_inc(v_typeName_181_);
v_struct_182_ = lean_ctor_get(v_e_138_, 2);
lean_inc_ref(v_struct_182_);
lean_dec_ref_known(v_e_138_, 3);
lean_inc_ref(v_visitConst_137_);
v___x_183_ = lean_apply_3(v_visitConst_137_, v_typeName_181_, v_acc_139_, v___x_158_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
v_snd_185_ = lean_ctor_get(v___x_183_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v___x_183_);
v_e_138_ = v_struct_182_;
v_acc_139_ = v_fst_184_;
v_a_140_ = v_snd_185_;
goto _start;
}
case 4:
{
lean_object* v_declName_187_; lean_object* v___x_188_; 
v_declName_187_ = lean_ctor_get(v_e_138_, 0);
lean_inc(v_declName_187_);
lean_dec_ref_known(v_e_138_, 2);
v___x_188_ = lean_apply_3(v_visitConst_137_, v_declName_187_, v_acc_139_, v___x_158_);
return v___x_188_;
}
default: 
{
lean_object* v___x_189_; 
lean_dec_ref(v_e_138_);
lean_dec_ref(v_visitConst_137_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_acc_139_);
lean_ctor_set(v___x_189_, 1, v___x_158_);
return v___x_189_;
}
}
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec_ref(v_e_138_);
lean_dec_ref(v_visitConst_137_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_acc_139_);
lean_ctor_set(v___x_194_, 1, v_a_140_);
return v___x_194_;
}
v___jp_141_:
{
lean_object* v___x_145_; lean_object* v_fst_146_; lean_object* v_snd_147_; 
lean_inc_ref(v_visitConst_137_);
v___x_145_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_137_, v_d_142_, v_acc_139_, v___y_144_);
v_fst_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_fst_146_);
v_snd_147_ = lean_ctor_get(v___x_145_, 1);
lean_inc(v_snd_147_);
lean_dec_ref(v___x_145_);
v_e_138_ = v_b_143_;
v_acc_139_ = v_fst_146_;
v_a_140_ = v_snd_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object* v_00_u03b1_195_, lean_object* v_visitConst_196_, lean_object* v_e_197_, lean_object* v_acc_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_196_, v_e_197_, v_acc_198_, v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object* v_00_u03b2_201_, lean_object* v_m_202_, lean_object* v_a_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_202_, v_a_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object* v_00_u03b2_205_, lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(v_00_u03b2_205_, v_m_206_, v_a_207_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_m_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object* v_00_u03b2_210_, lean_object* v_m_211_, lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_211_, v_a_212_, v_b_213_);
return v___x_214_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(lean_object* v_00_u03b2_215_, lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_219_, lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(v_00_u03b2_219_, v_a_220_, v_x_221_);
lean_dec(v_x_221_);
lean_dec_ref(v_a_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(lean_object* v_00_u03b2_224_, lean_object* v_data_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_data_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_227_, lean_object* v_i_228_, lean_object* v_source_229_, lean_object* v_target_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v_i_228_, v_source_229_, v_target_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_233_, v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0(lean_object* v_f_236_, lean_object* v_c_237_, lean_object* v_acc_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_visited_240_; lean_object* v_visitedConsts_241_; uint8_t v___x_242_; 
v_visited_240_ = lean_ctor_get(v___y_239_, 0);
v_visitedConsts_241_ = lean_ctor_get(v___y_239_, 1);
v___x_242_ = l_Lean_NameHashSet_contains(v_visitedConsts_241_, v_c_237_);
if (v___x_242_ == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
lean_inc_ref(v_visitedConsts_241_);
lean_inc_ref(v_visited_240_);
v_isSharedCheck_252_ = !lean_is_exclusive(v___y_239_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; 
v_unused_253_ = lean_ctor_get(v___y_239_, 1);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v___y_239_, 0);
lean_dec(v_unused_254_);
v___x_244_ = v___y_239_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_dec(v___y_239_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v_c_237_);
v___x_246_ = l_Lean_NameHashSet_insert(v_visitedConsts_241_, v_c_237_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_visited_240_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_apply_2(v_f_236_, v_c_237_, v_acc_238_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
return v___x_250_;
}
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v_c_237_);
lean_dec(v_f_236_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_acc_238_);
lean_ctor_set(v___x_255_, 1, v___y_239_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object* v_f_256_, lean_object* v_e_257_, lean_object* v_acc_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_visitConst_260_; lean_object* v___x_261_; 
v_visitConst_260_ = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___redArg___lam__0), 4, 1);
lean_closure_set(v_visitConst_260_, 0, v_f_256_);
v___x_261_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_visitConst_260_, v_e_257_, v_acc_258_, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* v_00_u03b1_262_, lean_object* v_f_263_, lean_object* v_e_264_, lean_object* v_acc_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_263_, v_e_264_, v_acc_265_, v_a_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(64u);
v___x_269_ = l_Lean_mkPtrSet___redArg(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_unsigned_to_nat(16u);
v___x_272_ = lean_mk_array(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2);
v___x_277_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object* v_e_279_, lean_object* v_init_280_, lean_object* v_f_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_fst_284_; 
v___x_282_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_283_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_281_, v_e_279_, v_init_280_, v___x_282_);
v_fst_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_fst_284_);
lean_dec_ref(v___x_283_);
return v_fst_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* v_00_u03b1_285_, lean_object* v_e_286_, lean_object* v_init_287_, lean_object* v_f_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_fst_291_; 
v___x_289_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_290_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v_f_288_, v_e_286_, v_init_287_, v___x_289_);
v_fst_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_fst_291_);
lean_dec_ref(v___x_290_);
return v_fst_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object* v_c_292_, lean_object* v_cs_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_array_push(v_cs_293_, v_c_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* v_e_298_){
_start:
{
lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_fst_303_; 
v___f_299_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__0));
v___x_300_ = ((lean_object*)(l_Lean_Expr_getUsedConstants___closed__1));
v___x_301_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_302_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_299_, v_e_298_, v___x_300_, v___x_301_);
v_fst_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_fst_303_);
lean_dec_ref(v___x_302_);
return v_fst_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object* v_c_304_, lean_object* v_cs_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_NameSet_insert(v_cs_305_, v_c_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* v_e_308_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_fst_313_; 
v___f_309_ = ((lean_object*)(l_Lean_Expr_getUsedConstantsAsSet___closed__0));
v___x_310_ = l_Lean_NameSet_empty;
v___x_311_ = lean_obj_once(&l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3, &l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once, _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3);
v___x_312_ = l_Lean_Expr_FoldConstsImpl_fold___redArg(v___f_309_, v_e_308_, v___x_310_, v___x_311_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_fst_313_);
lean_dec_ref(v___x_312_);
return v_fst_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* v_c_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = l_Lean_ConstantInfo_type(v_c_314_);
v___x_316_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_315_);
v___x_317_ = 1;
lean_inc_ref(v_c_314_);
v___x_318_ = l_Lean_ConstantInfo_value_x3f(v_c_314_, v___x_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
switch(lean_obj_tag(v_c_314_))
{
case 5:
{
lean_object* v_val_319_; lean_object* v_ctors_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_val_319_ = lean_ctor_get(v_c_314_, 0);
lean_inc_ref(v_val_319_);
lean_dec_ref_known(v_c_314_, 1);
v_ctors_320_ = lean_ctor_get(v_val_319_, 4);
lean_inc(v_ctors_320_);
lean_dec_ref(v_val_319_);
v___x_321_ = l_Lean_NameSet_ofList(v_ctors_320_);
lean_dec(v_ctors_320_);
v___x_322_ = l_Lean_NameSet_append(v___x_316_, v___x_321_);
return v___x_322_;
}
case 6:
{
lean_object* v_val_323_; lean_object* v_toConstantVal_324_; lean_object* v_name_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_val_323_ = lean_ctor_get(v_c_314_, 0);
lean_inc_ref(v_val_323_);
lean_dec_ref_known(v_c_314_, 1);
v_toConstantVal_324_ = lean_ctor_get(v_val_323_, 0);
lean_inc_ref(v_toConstantVal_324_);
lean_dec_ref(v_val_323_);
v_name_325_ = lean_ctor_get(v_toConstantVal_324_, 0);
lean_inc(v_name_325_);
lean_dec_ref(v_toConstantVal_324_);
v___x_326_ = l_Lean_NameSet_empty;
v___x_327_ = l_Lean_NameSet_insert(v___x_326_, v_name_325_);
v___x_328_ = l_Lean_NameSet_append(v___x_316_, v___x_327_);
return v___x_328_;
}
case 7:
{
lean_object* v_val_329_; lean_object* v_all_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_val_329_ = lean_ctor_get(v_c_314_, 0);
lean_inc_ref(v_val_329_);
lean_dec_ref_known(v_c_314_, 1);
v_all_330_ = lean_ctor_get(v_val_329_, 1);
lean_inc(v_all_330_);
lean_dec_ref(v_val_329_);
v___x_331_ = l_Lean_NameSet_ofList(v_all_330_);
lean_dec(v_all_330_);
v___x_332_ = l_Lean_NameSet_append(v___x_316_, v___x_331_);
return v___x_332_;
}
default: 
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec_ref(v_c_314_);
v___x_333_ = l_Lean_NameSet_empty;
v___x_334_ = l_Lean_NameSet_append(v___x_316_, v___x_333_);
return v___x_334_;
}
}
}
else
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_c_314_);
v_val_335_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_318_, 1);
v___x_336_ = l_Lean_Expr_getUsedConstantsAsSet(v_val_335_);
v___x_337_ = l_Lean_NameSet_append(v___x_316_, v___x_336_);
return v___x_337_;
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
