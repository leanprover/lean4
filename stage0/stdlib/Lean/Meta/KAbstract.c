// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0;
static lean_once_cell_t l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_kabstract___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_kabstract___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = lean_expr_eqv(v_key_4_, v_a_1_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg(lean_object* v_m_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_buckets_14_; lean_object* v___x_15_; uint64_t v___x_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v_fold_19_; uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; size_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_buckets_14_ = lean_ctor_get(v_m_12_, 1);
v___x_15_ = lean_array_get_size(v_buckets_14_);
v___x_16_ = l_Lean_Expr_hash(v_a_13_);
v___x_17_ = 32ULL;
v___x_18_ = lean_uint64_shift_right(v___x_16_, v___x_17_);
v_fold_19_ = lean_uint64_xor(v___x_16_, v___x_18_);
v___x_20_ = 16ULL;
v___x_21_ = lean_uint64_shift_right(v_fold_19_, v___x_20_);
v___x_22_ = lean_uint64_xor(v_fold_19_, v___x_21_);
v___x_23_ = lean_uint64_to_usize(v___x_22_);
v___x_24_ = lean_usize_of_nat(v___x_15_);
v___x_25_ = ((size_t)1ULL);
v___x_26_ = lean_usize_sub(v___x_24_, v___x_25_);
v___x_27_ = lean_usize_land(v___x_23_, v___x_26_);
v___x_28_ = lean_array_uget_borrowed(v_buckets_14_, v___x_27_);
v___x_29_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(v_a_13_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg___boxed(lean_object* v_m_30_, lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg(v_m_30_, v_a_31_);
lean_dec_ref(v_a_31_);
lean_dec_ref(v_m_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
return v_x_34_;
}
else
{
lean_object* v_key_36_; lean_object* v_value_37_; lean_object* v_tail_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_61_; 
v_key_36_ = lean_ctor_get(v_x_35_, 0);
v_value_37_ = lean_ctor_get(v_x_35_, 1);
v_tail_38_ = lean_ctor_get(v_x_35_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_61_ == 0)
{
v___x_40_ = v_x_35_;
v_isShared_41_ = v_isSharedCheck_61_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_tail_38_);
lean_inc(v_value_37_);
lean_inc(v_key_36_);
lean_dec(v_x_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_61_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v_fold_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v___x_49_; size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_42_ = lean_array_get_size(v_x_34_);
v___x_43_ = l_Lean_Expr_hash(v_key_36_);
v___x_44_ = 32ULL;
v___x_45_ = lean_uint64_shift_right(v___x_43_, v___x_44_);
v_fold_46_ = lean_uint64_xor(v___x_43_, v___x_45_);
v___x_47_ = 16ULL;
v___x_48_ = lean_uint64_shift_right(v_fold_46_, v___x_47_);
v___x_49_ = lean_uint64_xor(v_fold_46_, v___x_48_);
v___x_50_ = lean_uint64_to_usize(v___x_49_);
v___x_51_ = lean_usize_of_nat(v___x_42_);
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_sub(v___x_51_, v___x_52_);
v___x_54_ = lean_usize_land(v___x_50_, v___x_53_);
v___x_55_ = lean_array_uget_borrowed(v_x_34_, v___x_54_);
lean_inc(v___x_55_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 2, v___x_55_);
v___x_57_ = v___x_40_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_key_36_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_value_37_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v___x_55_);
v___x_57_ = v_reuseFailAlloc_60_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_array_uset(v_x_34_, v___x_54_, v___x_57_);
v_x_34_ = v___x_58_;
v_x_35_ = v_tail_38_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2___redArg(lean_object* v_i_62_, lean_object* v_source_63_, lean_object* v_target_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_get_size(v_source_63_);
v___x_66_ = lean_nat_dec_lt(v_i_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_dec_ref(v_source_63_);
lean_dec(v_i_62_);
return v_target_64_;
}
else
{
lean_object* v_es_67_; lean_object* v___x_68_; lean_object* v_source_69_; lean_object* v_target_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_es_67_ = lean_array_fget(v_source_63_, v_i_62_);
v___x_68_ = lean_box(0);
v_source_69_ = lean_array_fset(v_source_63_, v_i_62_, v___x_68_);
v_target_70_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4___redArg(v_target_64_, v_es_67_);
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_i_62_, v___x_71_);
lean_dec(v_i_62_);
v_i_62_ = v___x_72_;
v_source_63_ = v_source_69_;
v_target_64_ = v_target_70_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1___redArg(lean_object* v_data_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_nbuckets_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_75_ = lean_array_get_size(v_data_74_);
v___x_76_ = lean_unsigned_to_nat(2u);
v_nbuckets_77_ = lean_nat_mul(v___x_75_, v___x_76_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_box(0);
v___x_80_ = lean_mk_array(v_nbuckets_77_, v___x_79_);
v___x_81_ = lean_array_propagate_mark(v_data_74_, v___x_80_);
v___x_82_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2___redArg(v___x_78_, v_data_74_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0___redArg(lean_object* v_m_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v_size_86_; lean_object* v_buckets_87_; lean_object* v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v_fold_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v_bkt_101_; uint8_t v___x_102_; 
v_size_86_ = lean_ctor_get(v_m_83_, 0);
v_buckets_87_ = lean_ctor_get(v_m_83_, 1);
v___x_88_ = lean_array_get_size(v_buckets_87_);
v___x_89_ = l_Lean_Expr_hash(v_a_84_);
v___x_90_ = 32ULL;
v___x_91_ = lean_uint64_shift_right(v___x_89_, v___x_90_);
v_fold_92_ = lean_uint64_xor(v___x_89_, v___x_91_);
v___x_93_ = 16ULL;
v___x_94_ = lean_uint64_shift_right(v_fold_92_, v___x_93_);
v___x_95_ = lean_uint64_xor(v_fold_92_, v___x_94_);
v___x_96_ = lean_uint64_to_usize(v___x_95_);
v___x_97_ = lean_usize_of_nat(v___x_88_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_sub(v___x_97_, v___x_98_);
v___x_100_ = lean_usize_land(v___x_96_, v___x_99_);
v_bkt_101_ = lean_array_uget_borrowed(v_buckets_87_, v___x_100_);
v___x_102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(v_a_84_, v_bkt_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_123_; 
lean_inc_ref(v_buckets_87_);
lean_inc(v_size_86_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_m_83_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; 
v_unused_124_ = lean_ctor_get(v_m_83_, 1);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_m_83_, 0);
lean_dec(v_unused_125_);
v___x_104_ = v_m_83_;
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
else
{
lean_dec(v_m_83_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v_size_x27_107_; lean_object* v___x_108_; lean_object* v_buckets_x27_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v_size_x27_107_ = lean_nat_add(v_size_86_, v___x_106_);
lean_dec(v_size_86_);
lean_inc(v_bkt_101_);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v_a_84_);
lean_ctor_set(v___x_108_, 1, v_b_85_);
lean_ctor_set(v___x_108_, 2, v_bkt_101_);
v_buckets_x27_109_ = lean_array_uset(v_buckets_87_, v___x_100_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = lean_nat_mul(v_size_x27_107_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = lean_nat_div(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_array_get_size(v_buckets_x27_109_);
v___x_115_ = lean_nat_dec_le(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v_val_116_; lean_object* v___x_118_; 
v_val_116_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1___redArg(v_buckets_x27_109_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_val_116_);
lean_ctor_set(v___x_104_, 0, v_size_x27_107_);
v___x_118_ = v___x_104_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_size_x27_107_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_val_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_121_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_buckets_x27_109_);
lean_ctor_set(v___x_104_, 0, v_size_x27_107_);
v___x_121_ = v___x_104_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_size_x27_107_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_buckets_x27_109_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_dec(v_b_85_);
lean_dec_ref(v_a_84_);
return v_m_83_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_unsigned_to_nat(16u);
v___x_128_ = lean_mk_array(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0, &l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0_once, _init_l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__0);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(lean_object* v_e_132_, lean_object* v_p_133_, lean_object* v_occs_134_, lean_object* v_pHeadIdx_135_, lean_object* v_pNumArgs_136_, lean_object* v_offset_137_, lean_object* v_x_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
switch(lean_obj_tag(v_e_132_))
{
case 5:
{
lean_object* v_fn_145_; lean_object* v_arg_146_; lean_object* v___x_147_; 
v_fn_145_ = lean_ctor_get(v_e_132_, 0);
v_arg_146_ = lean_ctor_get(v_e_132_, 1);
lean_inc(v_offset_137_);
lean_inc_ref(v_fn_145_);
lean_inc_ref(v_p_133_);
v___x_147_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_fn_145_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
lean_inc_ref(v_arg_146_);
v___x_149_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_arg_146_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_171_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_171_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
size_t v___x_154_; size_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_ptr_addr(v_fn_145_);
v___x_155_ = lean_ptr_addr(v_a_148_);
v___x_156_ = lean_usize_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_dec_ref_known(v_e_132_, 2);
v___x_157_ = l_Lean_Expr_app___override(v_a_148_, v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_157_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
size_t v___x_161_; size_t v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_ptr_addr(v_arg_146_);
v___x_162_ = lean_ptr_addr(v_a_150_);
v___x_163_ = lean_usize_dec_eq(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref_known(v_e_132_, 2);
v___x_164_ = l_Lean_Expr_app___override(v_a_148_, v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_164_);
v___x_166_ = v___x_152_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
lean_dec(v_a_150_);
lean_dec(v_a_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v_e_132_);
v___x_169_ = v___x_152_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_e_132_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
else
{
lean_dec(v_a_148_);
lean_dec_ref_known(v_e_132_, 2);
return v___x_149_;
}
}
else
{
lean_dec_ref_known(v_e_132_, 2);
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
return v___x_147_;
}
}
case 10:
{
lean_object* v_data_172_; lean_object* v_expr_173_; lean_object* v___x_174_; 
v_data_172_ = lean_ctor_get(v_e_132_, 0);
v_expr_173_ = lean_ctor_get(v_e_132_, 1);
lean_inc_ref(v_expr_173_);
v___x_174_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_expr_173_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_189_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_189_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_ptr_addr(v_expr_173_);
v___x_180_ = lean_ptr_addr(v_a_175_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_inc(v_data_172_);
lean_dec_ref_known(v_e_132_, 2);
v___x_182_ = l_Lean_Expr_mdata___override(v_data_172_, v_a_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_182_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v_a_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_e_132_);
v___x_187_ = v___x_177_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_e_132_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_132_, 2);
return v___x_174_;
}
}
case 11:
{
lean_object* v_typeName_190_; lean_object* v_idx_191_; lean_object* v_struct_192_; lean_object* v___x_193_; 
v_typeName_190_ = lean_ctor_get(v_e_132_, 0);
v_idx_191_ = lean_ctor_get(v_e_132_, 1);
v_struct_192_ = lean_ctor_get(v_e_132_, 2);
lean_inc_ref(v_struct_192_);
v___x_193_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_struct_192_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_208_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_208_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_ptr_addr(v_struct_192_);
v___x_199_ = lean_ptr_addr(v_a_194_);
v___x_200_ = lean_usize_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_inc(v_idx_191_);
lean_inc(v_typeName_190_);
lean_dec_ref_known(v_e_132_, 3);
v___x_201_ = l_Lean_Expr_proj___override(v_typeName_190_, v_idx_191_, v_a_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_201_);
v___x_203_ = v___x_196_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_object* v___x_206_; 
lean_dec(v_a_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v_e_132_);
v___x_206_ = v___x_196_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_e_132_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_132_, 3);
return v___x_193_;
}
}
case 8:
{
lean_object* v_declName_209_; lean_object* v_type_210_; lean_object* v_value_211_; lean_object* v_body_212_; uint8_t v_nondep_213_; lean_object* v___x_214_; 
v_declName_209_ = lean_ctor_get(v_e_132_, 0);
v_type_210_ = lean_ctor_get(v_e_132_, 1);
v_value_211_ = lean_ctor_get(v_e_132_, 2);
v_body_212_ = lean_ctor_get(v_e_132_, 3);
v_nondep_213_ = lean_ctor_get_uint8(v_e_132_, sizeof(void*)*4 + 8);
lean_inc(v_offset_137_);
lean_inc_ref(v_type_210_);
lean_inc_ref(v_p_133_);
v___x_214_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_type_210_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
lean_inc(v_offset_137_);
lean_inc_ref(v_value_211_);
lean_inc_ref(v_p_133_);
v___x_216_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_value_211_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_offset_137_, v___x_218_);
lean_dec(v_offset_137_);
lean_inc_ref(v_body_212_);
v___x_220_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_body_212_, v___x_219_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_249_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_249_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_249_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_249_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
size_t v___x_225_; size_t v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_ptr_addr(v_type_210_);
v___x_226_ = lean_ptr_addr(v_a_215_);
v___x_227_ = lean_usize_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_inc(v_declName_209_);
lean_dec_ref_known(v_e_132_, 4);
v___x_228_ = l_Lean_Expr_letE___override(v_declName_209_, v_a_215_, v_a_217_, v_a_221_, v_nondep_213_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_228_);
v___x_230_ = v___x_223_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
else
{
size_t v___x_232_; size_t v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_ptr_addr(v_value_211_);
v___x_233_ = lean_ptr_addr(v_a_217_);
v___x_234_ = lean_usize_dec_eq(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_inc(v_declName_209_);
lean_dec_ref_known(v_e_132_, 4);
v___x_235_ = l_Lean_Expr_letE___override(v_declName_209_, v_a_215_, v_a_217_, v_a_221_, v_nondep_213_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_235_);
v___x_237_ = v___x_223_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
size_t v___x_239_; size_t v___x_240_; uint8_t v___x_241_; 
v___x_239_ = lean_ptr_addr(v_body_212_);
v___x_240_ = lean_ptr_addr(v_a_221_);
v___x_241_ = lean_usize_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_inc(v_declName_209_);
lean_dec_ref_known(v_e_132_, 4);
v___x_242_ = l_Lean_Expr_letE___override(v_declName_209_, v_a_215_, v_a_217_, v_a_221_, v_nondep_213_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_242_);
v___x_244_ = v___x_223_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
else
{
lean_object* v___x_247_; 
lean_dec(v_a_221_);
lean_dec(v_a_217_);
lean_dec(v_a_215_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v_e_132_);
v___x_247_ = v___x_223_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_e_132_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
else
{
lean_dec(v_a_217_);
lean_dec(v_a_215_);
lean_dec_ref_known(v_e_132_, 4);
return v___x_220_;
}
}
else
{
lean_dec(v_a_215_);
lean_dec_ref_known(v_e_132_, 4);
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
return v___x_216_;
}
}
else
{
lean_dec_ref_known(v_e_132_, 4);
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
return v___x_214_;
}
}
case 6:
{
lean_object* v_binderName_250_; lean_object* v_binderType_251_; lean_object* v_body_252_; uint8_t v_binderInfo_253_; lean_object* v___x_254_; 
v_binderName_250_ = lean_ctor_get(v_e_132_, 0);
v_binderType_251_ = lean_ctor_get(v_e_132_, 1);
v_body_252_ = lean_ctor_get(v_e_132_, 2);
v_binderInfo_253_ = lean_ctor_get_uint8(v_e_132_, sizeof(void*)*3 + 8);
lean_inc(v_offset_137_);
lean_inc_ref(v_binderType_251_);
lean_inc_ref(v_p_133_);
v___x_254_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_binderType_251_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_offset_137_, v___x_256_);
lean_dec(v_offset_137_);
lean_inc_ref(v_body_252_);
v___x_258_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_body_252_, v___x_257_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_285_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_285_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_285_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_285_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_ptr_addr(v_binderType_251_);
v___x_264_ = lean_ptr_addr(v_a_255_);
v___x_265_ = lean_usize_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_binderName_250_);
lean_dec_ref_known(v_e_132_, 3);
v___x_266_ = l_Lean_Expr_lam___override(v_binderName_250_, v_a_255_, v_a_259_, v_binderInfo_253_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_266_);
v___x_268_ = v___x_261_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
size_t v___x_270_; size_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_ptr_addr(v_body_252_);
v___x_271_ = lean_ptr_addr(v_a_259_);
v___x_272_ = lean_usize_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_binderName_250_);
lean_dec_ref_known(v_e_132_, 3);
v___x_273_ = l_Lean_Expr_lam___override(v_binderName_250_, v_a_255_, v_a_259_, v_binderInfo_253_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_273_);
v___x_275_ = v___x_261_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
else
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_253_, v_binderInfo_253_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_inc(v_binderName_250_);
lean_dec_ref_known(v_e_132_, 3);
v___x_278_ = l_Lean_Expr_lam___override(v_binderName_250_, v_a_255_, v_a_259_, v_binderInfo_253_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_278_);
v___x_280_ = v___x_261_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v_a_259_);
lean_dec(v_a_255_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_e_132_);
v___x_283_ = v___x_261_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_e_132_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
else
{
lean_dec(v_a_255_);
lean_dec_ref_known(v_e_132_, 3);
return v___x_258_;
}
}
else
{
lean_dec_ref_known(v_e_132_, 3);
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
return v___x_254_;
}
}
case 7:
{
lean_object* v_binderName_286_; lean_object* v_binderType_287_; lean_object* v_body_288_; uint8_t v_binderInfo_289_; lean_object* v___x_290_; 
v_binderName_286_ = lean_ctor_get(v_e_132_, 0);
v_binderType_287_ = lean_ctor_get(v_e_132_, 1);
v_body_288_ = lean_ctor_get(v_e_132_, 2);
v_binderInfo_289_ = lean_ctor_get_uint8(v_e_132_, sizeof(void*)*3 + 8);
lean_inc(v_offset_137_);
lean_inc_ref(v_binderType_287_);
lean_inc_ref(v_p_133_);
v___x_290_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_binderType_287_, v_offset_137_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_offset_137_, v___x_292_);
lean_dec(v_offset_137_);
lean_inc_ref(v_body_288_);
v___x_294_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_133_, v_occs_134_, v_pHeadIdx_135_, v_pNumArgs_136_, v_body_288_, v___x_293_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_321_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_321_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_321_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_321_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_ptr_addr(v_binderType_287_);
v___x_300_ = lean_ptr_addr(v_a_291_);
v___x_301_ = lean_usize_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_binderName_286_);
lean_dec_ref_known(v_e_132_, 3);
v___x_302_ = l_Lean_Expr_forallE___override(v_binderName_286_, v_a_291_, v_a_295_, v_binderInfo_289_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_302_);
v___x_304_ = v___x_297_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_ptr_addr(v_body_288_);
v___x_307_ = lean_ptr_addr(v_a_295_);
v___x_308_ = lean_usize_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_binderName_286_);
lean_dec_ref_known(v_e_132_, 3);
v___x_309_ = l_Lean_Expr_forallE___override(v_binderName_286_, v_a_291_, v_a_295_, v_binderInfo_289_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_309_);
v___x_311_ = v___x_297_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_289_, v_binderInfo_289_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_316_; 
lean_inc(v_binderName_286_);
lean_dec_ref_known(v_e_132_, 3);
v___x_314_ = l_Lean_Expr_forallE___override(v_binderName_286_, v_a_291_, v_a_295_, v_binderInfo_289_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_314_);
v___x_316_ = v___x_297_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
else
{
lean_object* v___x_319_; 
lean_dec(v_a_295_);
lean_dec(v_a_291_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v_e_132_);
v___x_319_ = v___x_297_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_e_132_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
else
{
lean_dec(v_a_291_);
lean_dec_ref_known(v_e_132_, 3);
return v___x_294_;
}
}
else
{
lean_dec_ref_known(v_e_132_, 3);
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
return v___x_290_;
}
}
default: 
{
lean_object* v___x_322_; 
lean_dec(v_offset_137_);
lean_dec_ref(v_p_133_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_e_132_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object* v_p_323_, lean_object* v_occs_324_, lean_object* v_pHeadIdx_325_, lean_object* v_pNumArgs_326_, lean_object* v_e_327_, lean_object* v_offset_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
uint8_t v___y_336_; lean_object* v___y_337_; lean_object* v_r_338_; lean_object* v___y_339_; uint8_t v___y_360_; lean_object* v___y_361_; uint8_t v___y_366_; uint8_t v___y_445_; 
switch(lean_obj_tag(v_e_327_))
{
case 5:
{
uint8_t v___x_450_; 
v___x_450_ = 1;
v___y_445_ = v___x_450_;
goto v___jp_444_;
}
case 10:
{
uint8_t v___x_451_; 
v___x_451_ = 1;
v___y_445_ = v___x_451_;
goto v___jp_444_;
}
case 11:
{
uint8_t v___x_452_; 
v___x_452_ = 1;
v___y_445_ = v___x_452_;
goto v___jp_444_;
}
case 8:
{
uint8_t v___x_453_; 
v___x_453_ = 1;
v___y_445_ = v___x_453_;
goto v___jp_444_;
}
case 6:
{
uint8_t v___x_454_; 
v___x_454_ = 1;
v___y_445_ = v___x_454_;
goto v___jp_444_;
}
case 7:
{
uint8_t v___x_455_; 
v___x_455_ = 1;
v___y_445_ = v___x_455_;
goto v___jp_444_;
}
default: 
{
uint8_t v___x_456_; 
v___x_456_ = 0;
v___y_445_ = v___x_456_;
goto v___jp_444_;
}
}
v___jp_335_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_st_ref_get(v___y_339_);
if (v___y_336_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v___x_340_);
lean_dec(v___y_337_);
lean_dec_ref(v_e_327_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_r_338_);
return v___x_341_;
}
else
{
lean_object* v_fst_342_; uint8_t v___x_343_; 
v_fst_342_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_fst_342_);
lean_dec(v___x_340_);
v___x_343_ = lean_nat_dec_eq(v_fst_342_, v___y_337_);
lean_dec(v___y_337_);
lean_dec(v_fst_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec_ref(v_e_327_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_r_338_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_358_; 
v___x_345_ = lean_st_ref_take(v___y_339_);
v_fst_346_ = lean_ctor_get(v___x_345_, 0);
v_snd_347_ = lean_ctor_get(v___x_345_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_349_ = v___x_345_;
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_inc(v_fst_346_);
lean_dec(v___x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_box(0);
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0___redArg(v_snd_347_, v_e_327_, v___x_351_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_352_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_fst_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_st_ref_put(v___y_339_, v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_r_338_);
return v___x_356_;
}
}
}
}
}
v___jp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(0);
lean_inc_ref(v_e_327_);
v___x_363_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(v_e_327_, v_p_323_, v_occs_324_, v_pHeadIdx_325_, v_pNumArgs_326_, v_offset_328_, v___x_362_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___y_336_ = v___y_360_;
v___y_337_ = v___y_361_;
v_r_338_ = v_a_364_;
v___y_339_ = v_a_329_;
goto v___jp_335_;
}
else
{
lean_dec(v___y_361_);
lean_dec_ref(v_e_327_);
return v___x_363_;
}
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v_fst_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_442_; 
v___x_367_ = lean_st_ref_get(v_a_329_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_367_, 1);
lean_dec(v_unused_443_);
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_442_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_fst_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_442_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_Expr_hasLooseBVars(v_e_327_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
lean_inc_ref(v_e_327_);
v___x_373_ = l_Lean_Expr_toHeadIndex(v_e_327_);
v___x_374_ = l_Lean_instBEqHeadIndex_beq(v___x_373_, v_pHeadIdx_325_);
lean_dec(v___x_373_);
if (v___x_374_ == 0)
{
lean_del_object(v___x_370_);
v___y_360_ = v___y_366_;
v___y_361_ = v_fst_368_;
goto v___jp_359_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_Expr_headNumArgs(v_e_327_);
v___x_376_ = lean_nat_dec_eq(v___x_375_, v_pNumArgs_326_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
lean_del_object(v___x_370_);
v___y_360_ = v___y_366_;
v___y_361_ = v_fst_368_;
goto v___jp_359_;
}
else
{
lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_get(v_a_331_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_mctx_378_);
lean_dec(v___x_377_);
lean_inc_ref(v_p_323_);
lean_inc_ref(v_e_327_);
v___x_379_ = l_Lean_Meta_isExprDefEq(v_e_327_, v_p_323_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_430_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_430_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_430_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_430_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_unbox(v_a_380_);
lean_dec(v_a_380_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_del_object(v___x_382_);
lean_dec_ref(v_mctx_378_);
lean_del_object(v___x_370_);
v___x_385_ = lean_box(0);
lean_inc_ref(v_e_327_);
v___x_386_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(v_e_327_, v_p_323_, v_occs_324_, v_pHeadIdx_325_, v_pNumArgs_326_, v_offset_328_, v___x_385_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___y_336_ = v___y_366_;
v___y_337_ = v_fst_368_;
v_r_338_ = v_a_387_;
v___y_339_ = v_a_329_;
goto v___jp_335_;
}
else
{
lean_dec(v_fst_368_);
lean_dec_ref(v_e_327_);
return v___x_386_;
}
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Meta_Occurrences_contains(v_occs_324_, v_fst_368_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_382_);
lean_del_object(v___x_370_);
v___x_389_ = lean_st_ref_take(v_a_329_);
v_snd_390_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_389_, 0);
lean_dec(v_unused_418_);
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_fst_368_, v___x_394_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_snd_390_);
v___x_397_ = v_reuseFailAlloc_416_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_cache_400_; lean_object* v_zetaDeltaFVarIds_401_; lean_object* v_postponed_402_; lean_object* v_diag_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v___x_398_ = lean_st_ref_put(v_a_329_, v___x_397_);
v___x_399_ = lean_st_ref_take(v_a_331_);
v_cache_400_ = lean_ctor_get(v___x_399_, 1);
v_zetaDeltaFVarIds_401_ = lean_ctor_get(v___x_399_, 2);
v_postponed_402_ = lean_ctor_get(v___x_399_, 3);
v_diag_403_ = lean_ctor_get(v___x_399_, 4);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_415_);
v___x_405_ = v___x_399_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_diag_403_);
lean_inc(v_postponed_402_);
lean_inc(v_zetaDeltaFVarIds_401_);
lean_inc(v_cache_400_);
lean_dec(v___x_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_mctx_378_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_mctx_378_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_cache_400_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_zetaDeltaFVarIds_401_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_postponed_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_diag_403_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_st_ref_put(v_a_331_, v___x_408_);
v___x_410_ = lean_box(0);
lean_inc_ref(v_e_327_);
v___x_411_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(v_e_327_, v_p_323_, v_occs_324_, v_pHeadIdx_325_, v_pNumArgs_326_, v_offset_328_, v___x_410_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___y_336_ = v___y_366_;
v___y_337_ = v_fst_368_;
v_r_338_ = v_a_412_;
v___y_339_ = v_a_329_;
goto v___jp_335_;
}
else
{
lean_dec(v_fst_368_);
lean_dec_ref(v_e_327_);
return v___x_411_;
}
}
}
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec_ref(v_mctx_378_);
lean_dec_ref(v_e_327_);
lean_dec_ref(v_p_323_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_add(v_fst_368_, v___x_419_);
lean_dec(v_fst_368_);
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1, &l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1_once, _init_l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v___x_421_);
lean_ctor_set(v___x_370_, 0, v___x_420_);
v___x_423_ = v___x_370_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_429_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_424_ = lean_st_ref_swap(v_a_329_, v___x_423_);
lean_dec(v___x_424_);
v___x_425_ = l_Lean_mkBVar(v_offset_328_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_425_);
v___x_427_ = v___x_382_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_mctx_378_);
lean_del_object(v___x_370_);
lean_dec(v_fst_368_);
lean_dec(v_offset_328_);
lean_dec_ref(v_e_327_);
lean_dec_ref(v_p_323_);
v_a_431_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_379_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_379_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_del_object(v___x_370_);
v___x_439_ = lean_box(0);
lean_inc_ref(v_e_327_);
v___x_440_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(v_e_327_, v_p_323_, v_occs_324_, v_pHeadIdx_325_, v_pNumArgs_326_, v_offset_328_, v___x_439_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___y_336_ = v___y_366_;
v___y_337_ = v_fst_368_;
v_r_338_ = v_a_441_;
v___y_339_ = v_a_329_;
goto v___jp_335_;
}
else
{
lean_dec(v_fst_368_);
lean_dec_ref(v_e_327_);
return v___x_440_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_st_ref_get(v_a_329_);
if (v___y_445_ == 0)
{
lean_dec(v___x_446_);
v___y_366_ = v___y_445_;
goto v___jp_365_;
}
else
{
lean_object* v_snd_447_; uint8_t v___x_448_; 
v_snd_447_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_447_);
lean_dec(v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg(v_snd_447_, v_e_327_);
lean_dec(v_snd_447_);
if (v___x_448_ == 0)
{
v___y_366_ = v___y_445_;
goto v___jp_365_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_offset_328_);
lean_dec_ref(v_p_323_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_e_327_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object* v_p_457_, lean_object* v_occs_458_, lean_object* v_pHeadIdx_459_, lean_object* v_pNumArgs_460_, lean_object* v_e_461_, lean_object* v_offset_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_457_, v_occs_458_, v_pHeadIdx_459_, v_pNumArgs_460_, v_e_461_, v_offset_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec(v_pNumArgs_460_);
lean_dec(v_pHeadIdx_459_);
lean_dec(v_occs_458_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0___boxed(lean_object* v_e_470_, lean_object* v_p_471_, lean_object* v_occs_472_, lean_object* v_pHeadIdx_473_, lean_object* v_pNumArgs_474_, lean_object* v_offset_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___lam__0(v_e_470_, v_p_471_, v_occs_472_, v_pHeadIdx_473_, v_pNumArgs_474_, v_offset_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec(v_pNumArgs_474_);
lean_dec(v_pHeadIdx_473_);
lean_dec(v_occs_472_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0(lean_object* v_00_u03b2_484_, lean_object* v_m_485_, lean_object* v_a_486_, lean_object* v_b_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0___redArg(v_m_485_, v_a_486_, v_b_487_);
return v___x_488_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1(lean_object* v_00_u03b2_489_, lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___redArg(v_m_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1___boxed(lean_object* v_00_u03b2_493_, lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__1(v_00_u03b2_493_, v_m_494_, v_a_495_);
lean_dec_ref(v_a_495_);
lean_dec_ref(v_m_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0(lean_object* v_00_u03b2_498_, lean_object* v_a_499_, lean_object* v_x_500_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___redArg(v_a_499_, v_x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_502_, lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__0(v_00_u03b2_502_, v_a_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec_ref(v_a_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1(lean_object* v_00_u03b2_507_, lean_object* v_data_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1___redArg(v_data_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_510_, lean_object* v_i_511_, lean_object* v_source_512_, lean_object* v_target_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2___redArg(v_i_511_, v_source_512_, v_target_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit_spec__0_spec__1_spec__2_spec__4___redArg(v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object* v_e_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Expr_hasMVar(v_e_519_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_e_519_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v_mctx_525_; lean_object* v___x_526_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_529_; lean_object* v_cache_530_; lean_object* v_zetaDeltaFVarIds_531_; lean_object* v_postponed_532_; lean_object* v_diag_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
v___x_524_ = lean_st_ref_get(v___y_520_);
v_mctx_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_ref(v_mctx_525_);
lean_dec(v___x_524_);
v___x_526_ = l_Lean_instantiateMVarsCore(v_mctx_525_, v_e_519_);
v_fst_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_fst_527_);
v_snd_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_snd_528_);
lean_dec_ref(v___x_526_);
v___x_529_ = lean_st_ref_take(v___y_520_);
v_cache_530_ = lean_ctor_get(v___x_529_, 1);
v_zetaDeltaFVarIds_531_ = lean_ctor_get(v___x_529_, 2);
v_postponed_532_ = lean_ctor_get(v___x_529_, 3);
v_diag_533_ = lean_ctor_get(v___x_529_, 4);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v___x_529_, 0);
lean_dec(v_unused_543_);
v___x_535_ = v___x_529_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_diag_533_);
lean_inc(v_postponed_532_);
lean_inc(v_zetaDeltaFVarIds_531_);
lean_inc(v_cache_530_);
lean_dec(v___x_529_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_snd_528_);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_snd_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_cache_530_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_zetaDeltaFVarIds_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_postponed_532_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_diag_533_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_put(v___y_520_, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_fst_527_);
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object* v_e_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_544_, v___y_545_);
lean_dec(v___y_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object* v_e_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_548_, v___y_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object* v_e_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(v_e_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_Meta_kabstract___closed__0(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1, &l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1_once, _init_l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___closed__1);
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* v_e_565_, lean_object* v_p_566_, lean_object* v_occs_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_604_; 
v___x_573_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_565_, v_a_569_);
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_604_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_604_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_604_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Expr_isFVar(v_p_566_);
if (v___x_594_ == 0)
{
lean_del_object(v___x_576_);
goto v___jp_578_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_box(0);
lean_inc(v_occs_567_);
v___x_596_ = l_Lean_Meta_instBEqOccurrences_beq(v_occs_567_, v___x_595_);
if (v___x_596_ == 0)
{
lean_del_object(v___x_576_);
goto v___jp_578_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_occs_567_);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
v___x_599_ = lean_array_push(v___x_598_, v_p_566_);
v___x_600_ = lean_expr_abstract(v_a_574_, v___x_599_);
lean_dec_ref(v___x_599_);
lean_dec(v_a_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_600_);
v___x_602_ = v___x_576_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
v___jp_578_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc_ref(v_p_566_);
v___x_579_ = l_Lean_Expr_toHeadIndex(v_p_566_);
v___x_580_ = l_Lean_Expr_headNumArgs(v_p_566_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_obj_once(&l_Lean_Meta_kabstract___closed__0, &l_Lean_Meta_kabstract___closed__0_once, _init_l_Lean_Meta_kabstract___closed__0);
v___x_583_ = lean_st_mk_ref(v___x_582_);
v___x_584_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_566_, v_occs_567_, v___x_579_, v___x_580_, v_a_574_, v___x_581_, v___x_583_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v___x_580_);
lean_dec(v___x_579_);
lean_dec(v_occs_567_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_st_ref_get(v___x_583_);
lean_dec(v___x_583_);
lean_dec(v___x_589_);
if (v_isShared_588_ == 0)
{
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_dec(v___x_583_);
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* v_e_605_, lean_object* v_p_606_, lean_object* v_occs_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_kabstract(v_e_605_, v_p_606_, v_occs_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_613_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_KAbstract(builtin);
}
#ifdef __cplusplus
}
#endif
