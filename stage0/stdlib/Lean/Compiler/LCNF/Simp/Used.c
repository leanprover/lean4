// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Used
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
v___x_6_ = l_Lean_instBEqFVarId_beq(v_key_4_, v_a_1_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
return v_x_12_;
}
else
{
lean_object* v_key_14_; lean_object* v_value_15_; lean_object* v_tail_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_39_; 
v_key_14_ = lean_ctor_get(v_x_13_, 0);
v_value_15_ = lean_ctor_get(v_x_13_, 1);
v_tail_16_ = lean_ctor_get(v_x_13_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_39_ == 0)
{
v___x_18_ = v_x_13_;
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_tail_16_);
lean_inc(v_value_15_);
lean_inc(v_key_14_);
lean_dec(v_x_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v_fold_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_20_ = lean_array_get_size(v_x_12_);
v___x_21_ = l_Lean_instHashableFVarId_hash(v_key_14_);
v___x_22_ = 32ULL;
v___x_23_ = lean_uint64_shift_right(v___x_21_, v___x_22_);
v_fold_24_ = lean_uint64_xor(v___x_21_, v___x_23_);
v___x_25_ = 16ULL;
v___x_26_ = lean_uint64_shift_right(v_fold_24_, v___x_25_);
v___x_27_ = lean_uint64_xor(v_fold_24_, v___x_26_);
v___x_28_ = lean_uint64_to_usize(v___x_27_);
v___x_29_ = lean_usize_of_nat(v___x_20_);
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v___x_29_, v___x_30_);
v___x_32_ = lean_usize_land(v___x_28_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_x_12_, v___x_32_);
lean_inc(v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v___x_33_);
v___x_35_ = v___x_18_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_key_14_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_value_15_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_33_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_array_uset(v_x_12_, v___x_32_, v___x_35_);
v_x_12_ = v___x_36_;
v_x_13_ = v_tail_16_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_40_, lean_object* v_source_41_, lean_object* v_target_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_array_get_size(v_source_41_);
v___x_44_ = lean_nat_dec_lt(v_i_40_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_source_41_);
lean_dec(v_i_40_);
return v_target_42_;
}
else
{
lean_object* v_es_45_; lean_object* v___x_46_; lean_object* v_source_47_; lean_object* v_target_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_es_45_ = lean_array_fget(v_source_41_, v_i_40_);
v___x_46_ = lean_box(0);
v_source_47_ = lean_array_fset(v_source_41_, v_i_40_, v___x_46_);
v_target_48_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_42_, v_es_45_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_i_40_, v___x_49_);
lean_dec(v_i_40_);
v_i_40_ = v___x_50_;
v_source_41_ = v_source_47_;
v_target_42_ = v_target_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(lean_object* v_data_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v___x_56_, v_data_52_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = l_Lean_instHashableFVarId_hash(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object* v_fvarId_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; lean_object* v_subst_107_; lean_object* v_used_108_; lean_object* v_binderRenaming_109_; lean_object* v_funDeclInfoMap_110_; uint8_t v_simplified_111_; lean_object* v_visited_112_; lean_object* v_inline_113_; lean_object* v_inlineLocal_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_125_; 
v___x_106_ = lean_st_ref_take(v_a_104_);
v_subst_107_ = lean_ctor_get(v___x_106_, 0);
v_used_108_ = lean_ctor_get(v___x_106_, 1);
v_binderRenaming_109_ = lean_ctor_get(v___x_106_, 2);
v_funDeclInfoMap_110_ = lean_ctor_get(v___x_106_, 3);
v_simplified_111_ = lean_ctor_get_uint8(v___x_106_, sizeof(void*)*7);
v_visited_112_ = lean_ctor_get(v___x_106_, 4);
v_inline_113_ = lean_ctor_get(v___x_106_, 5);
v_inlineLocal_114_ = lean_ctor_get(v___x_106_, 6);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_125_ == 0)
{
v___x_116_ = v___x_106_;
v_isShared_117_ = v_isSharedCheck_125_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_inlineLocal_114_);
lean_inc(v_inline_113_);
lean_inc(v_visited_112_);
lean_inc(v_funDeclInfoMap_110_);
lean_inc(v_binderRenaming_109_);
lean_inc(v_used_108_);
lean_inc(v_subst_107_);
lean_dec(v___x_106_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_125_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_118_ = lean_box(0);
v___x_119_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_used_108_, v_fvarId_103_, v___x_118_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_119_);
v___x_121_ = v___x_116_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_subst_107_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_binderRenaming_109_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v_funDeclInfoMap_110_);
lean_ctor_set(v_reuseFailAlloc_124_, 4, v_visited_112_);
lean_ctor_set(v_reuseFailAlloc_124_, 5, v_inline_113_);
lean_ctor_set(v_reuseFailAlloc_124_, 6, v_inlineLocal_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, sizeof(void*)*7, v_simplified_111_);
v___x_121_ = v_reuseFailAlloc_124_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_st_ref_set(v_a_104_, v___x_121_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_118_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(lean_object* v_fvarId_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_126_, v_a_127_);
lean_dec(v_a_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object* v_fvarId_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_130_, v_a_132_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object* v_fvarId_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar(v_fvarId_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0(lean_object* v_00_u03b2_150_, lean_object* v_m_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_m_151_, v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(lean_object* v_00_u03b2_155_, lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_156_, v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_159_, lean_object* v_a_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(v_00_u03b2_159_, v_a_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec(v_a_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1(lean_object* v_00_u03b2_164_, lean_object* v_data_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_data_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_167_, lean_object* v_i_168_, lean_object* v_source_169_, lean_object* v_target_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v_i_168_, v_source_169_, v_target_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_173_, v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object* v_arg_176_, lean_object* v_a_177_){
_start:
{
if (lean_obj_tag(v_arg_176_) == 1)
{
lean_object* v_fvarId_179_; lean_object* v___x_180_; 
v_fvarId_179_ = lean_ctor_get(v_arg_176_, 0);
lean_inc(v_fvarId_179_);
lean_dec_ref(v_arg_176_);
v___x_180_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_179_, v_a_177_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_arg_176_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(lean_object* v_arg_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_183_, v_a_184_);
lean_dec(v_a_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg(lean_object* v_arg_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_187_, v_a_189_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(lean_object* v_arg_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(v_arg_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object* v_as_207_, size_t v_i_208_, size_t v_stop_209_, lean_object* v_b_210_, lean_object* v___y_211_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = lean_usize_dec_eq(v_i_208_, v_stop_209_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_array_uget_borrowed(v_as_207_, v_i_208_);
lean_inc(v___x_214_);
v___x_215_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_214_, v___y_211_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; size_t v___x_217_; size_t v___x_218_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_208_, v___x_217_);
v_i_208_ = v___x_218_;
v_b_210_ = v_a_216_;
goto _start;
}
else
{
return v___x_215_;
}
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_b_210_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_stop_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
size_t v_i_boxed_227_; size_t v_stop_boxed_228_; lean_object* v_res_229_; 
v_i_boxed_227_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_stop_boxed_228_ = lean_unbox_usize(v_stop_223_);
lean_dec(v_stop_223_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_221_, v_i_boxed_227_, v_stop_boxed_228_, v_b_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v_as_221_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue(lean_object* v_e_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
switch(lean_obj_tag(v_e_230_))
{
case 0:
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
v_isSharedCheck_246_ = !lean_is_exclusive(v_e_230_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v_e_230_, 0);
lean_dec(v_unused_247_);
v___x_240_ = v_e_230_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_e_230_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
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
}
case 1:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
case 2:
{
lean_object* v_struct_250_; lean_object* v___x_251_; 
v_struct_250_ = lean_ctor_get(v_e_230_, 2);
lean_inc(v_struct_250_);
lean_dec_ref(v_e_230_);
v___x_251_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_250_, v_a_232_);
return v___x_251_;
}
case 3:
{
lean_object* v_args_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_args_252_ = lean_ctor_get(v_e_230_, 2);
lean_inc_ref(v_args_252_);
lean_dec_ref(v_e_230_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_get_size(v_args_252_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_nat_dec_lt(v___x_253_, v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec_ref(v_args_252_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
return v___x_257_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_le(v___x_254_, v___x_254_);
if (v___x_258_ == 0)
{
if (v___x_256_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v_args_252_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_255_);
return v___x_259_;
}
else
{
size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; 
v___x_260_ = ((size_t)0ULL);
v___x_261_ = lean_usize_of_nat(v___x_254_);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_252_, v___x_260_, v___x_261_, v___x_255_, v_a_232_);
lean_dec_ref(v_args_252_);
return v___x_262_;
}
}
else
{
size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v___x_263_ = ((size_t)0ULL);
v___x_264_ = lean_usize_of_nat(v___x_254_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_252_, v___x_263_, v___x_264_, v___x_255_, v_a_232_);
lean_dec_ref(v_args_252_);
return v___x_265_;
}
}
}
default: 
{
lean_object* v_fvarId_266_; lean_object* v_args_267_; lean_object* v___x_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_289_; 
v_fvarId_266_ = lean_ctor_get(v_e_230_, 0);
lean_inc(v_fvarId_266_);
v_args_267_ = lean_ctor_get(v_e_230_, 1);
lean_inc_ref(v_args_267_);
lean_dec_ref(v_e_230_);
v___x_268_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_266_, v_a_232_);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_268_, 0);
lean_dec(v_unused_290_);
v___x_270_ = v___x_268_;
v_isShared_271_ = v_isSharedCheck_289_;
goto v_resetjp_269_;
}
else
{
lean_dec(v___x_268_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_289_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_array_get_size(v_args_267_);
v___x_274_ = lean_box(0);
v___x_275_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v_args_267_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_277_ = v___x_270_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_274_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___x_273_, v___x_273_);
if (v___x_279_ == 0)
{
if (v___x_275_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_args_267_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_281_ = v___x_270_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_274_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_270_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_273_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_267_, v___x_283_, v___x_284_, v___x_274_, v_a_232_);
lean_dec_ref(v_args_267_);
return v___x_285_;
}
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_270_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_273_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_267_, v___x_286_, v___x_287_, v___x_274_, v_a_232_);
lean_dec_ref(v_args_267_);
return v___x_288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_301_, v_i_302_, v_stop_303_, v_b_304_, v___y_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
size_t v_i_boxed_326_; size_t v_stop_boxed_327_; lean_object* v_res_328_; 
v_i_boxed_326_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_327_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_314_, v_i_boxed_326_, v_stop_boxed_327_, v_b_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_as_314_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* v_letDecl_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_value_338_; lean_object* v___x_339_; 
v_value_338_ = lean_ctor_get(v_letDecl_329_, 3);
lean_inc(v_value_338_);
lean_dec_ref(v_letDecl_329_);
v___x_339_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_value_338_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* v_letDecl_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object* v_as_350_, size_t v_i_351_, size_t v_stop_352_, lean_object* v_b_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_351_, v_stop_352_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_array_uget_borrowed(v_as_350_, v_i_351_);
switch(lean_obj_tag(v___x_370_))
{
case 0:
{
lean_object* v_code_371_; 
v_code_371_ = lean_ctor_get(v___x_370_, 2);
lean_inc_ref(v_code_371_);
v___y_363_ = v_code_371_;
goto v___jp_362_;
}
case 1:
{
lean_object* v_code_372_; 
v_code_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc_ref(v_code_372_);
v___y_363_ = v_code_372_;
goto v___jp_362_;
}
default: 
{
lean_object* v_code_373_; 
v_code_373_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_code_373_);
v___y_363_ = v_code_373_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_b_353_);
return v___x_374_;
}
v___jp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v___y_363_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; size_t v___x_366_; size_t v___x_367_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_351_, v___x_366_);
v_i_351_ = v___x_367_;
v_b_353_ = v_a_365_;
goto _start;
}
else
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* v_code_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_decl_385_; lean_object* v_k_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; 
switch(lean_obj_tag(v_code_375_))
{
case 0:
{
lean_object* v_decl_396_; lean_object* v_k_397_; lean_object* v___x_398_; 
v_decl_396_ = lean_ctor_get(v_code_375_, 0);
lean_inc_ref(v_decl_396_);
v_k_397_ = lean_ctor_get(v_code_375_, 1);
lean_inc_ref(v_k_397_);
lean_dec_ref(v_code_375_);
v___x_398_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_396_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_dec_ref(v___x_398_);
v_code_375_ = v_k_397_;
goto _start;
}
else
{
lean_dec_ref(v_k_397_);
return v___x_398_;
}
}
case 3:
{
lean_object* v_fvarId_400_; lean_object* v_args_401_; lean_object* v___x_402_; 
v_fvarId_400_ = lean_ctor_get(v_code_375_, 0);
lean_inc(v_fvarId_400_);
v_args_401_ = lean_ctor_get(v_code_375_, 1);
lean_inc_ref(v_args_401_);
lean_dec_ref(v_code_375_);
v___x_402_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_400_, v_a_377_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_424_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_423_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_423_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_array_get_size(v_args_401_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_nat_dec_lt(v___x_406_, v___x_407_);
if (v___x_409_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_args_401_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_408_);
v___x_411_ = v___x_404_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_408_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_le(v___x_407_, v___x_407_);
if (v___x_413_ == 0)
{
if (v___x_409_ == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v_args_401_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_408_);
v___x_415_ = v___x_404_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_408_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
lean_del_object(v___x_404_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_407_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_401_, v___x_417_, v___x_418_, v___x_408_, v_a_377_);
lean_dec_ref(v_args_401_);
return v___x_419_;
}
}
else
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
lean_del_object(v___x_404_);
v___x_420_ = ((size_t)0ULL);
v___x_421_ = lean_usize_of_nat(v___x_407_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_401_, v___x_420_, v___x_421_, v___x_408_, v_a_377_);
lean_dec_ref(v_args_401_);
return v___x_422_;
}
}
}
}
else
{
lean_dec_ref(v_args_401_);
return v___x_402_;
}
}
case 4:
{
lean_object* v_cases_425_; lean_object* v_discr_426_; lean_object* v_alts_427_; lean_object* v___x_428_; 
v_cases_425_ = lean_ctor_get(v_code_375_, 0);
lean_inc_ref(v_cases_425_);
lean_dec_ref(v_code_375_);
v_discr_426_ = lean_ctor_get(v_cases_425_, 2);
lean_inc(v_discr_426_);
v_alts_427_ = lean_ctor_get(v_cases_425_, 3);
lean_inc_ref(v_alts_427_);
lean_dec_ref(v_cases_425_);
v___x_428_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_426_, v_a_377_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_450_);
v___x_430_ = v___x_428_;
v_isShared_431_ = v_isSharedCheck_449_;
goto v_resetjp_429_;
}
else
{
lean_dec(v___x_428_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_449_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_alts_427_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_437_; 
lean_dec_ref(v_alts_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_434_);
v___x_437_ = v___x_430_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_434_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_le(v___x_433_, v___x_433_);
if (v___x_439_ == 0)
{
if (v___x_435_ == 0)
{
lean_object* v___x_441_; 
lean_dec_ref(v_alts_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_434_);
v___x_441_ = v___x_430_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_434_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
lean_del_object(v___x_430_);
v___x_443_ = ((size_t)0ULL);
v___x_444_ = lean_usize_of_nat(v___x_433_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_427_, v___x_443_, v___x_444_, v___x_434_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_alts_427_);
return v___x_445_;
}
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
lean_del_object(v___x_430_);
v___x_446_ = ((size_t)0ULL);
v___x_447_ = lean_usize_of_nat(v___x_433_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_427_, v___x_446_, v___x_447_, v___x_434_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_alts_427_);
return v___x_448_;
}
}
}
}
else
{
lean_dec_ref(v_alts_427_);
return v___x_428_;
}
}
case 5:
{
lean_object* v_fvarId_451_; lean_object* v___x_452_; 
v_fvarId_451_ = lean_ctor_get(v_code_375_, 0);
lean_inc(v_fvarId_451_);
lean_dec_ref(v_code_375_);
v___x_452_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_451_, v_a_377_);
return v___x_452_;
}
case 6:
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
v_isSharedCheck_460_ = !lean_is_exclusive(v_code_375_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_code_375_, 0);
lean_dec(v_unused_461_);
v___x_454_ = v_code_375_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_code_375_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 0);
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
default: 
{
lean_object* v_decl_462_; lean_object* v_k_463_; 
v_decl_462_ = lean_ctor_get(v_code_375_, 0);
lean_inc_ref(v_decl_462_);
v_k_463_ = lean_ctor_get(v_code_375_, 1);
lean_inc_ref(v_k_463_);
lean_dec_ref(v_code_375_);
v_decl_385_ = v_decl_462_;
v_k_386_ = v_k_463_;
v___y_387_ = v_a_376_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
v___y_390_ = v_a_379_;
v___y_391_ = v_a_380_;
v___y_392_ = v_a_381_;
v___y_393_ = v_a_382_;
goto v___jp_384_;
}
}
v___jp_384_:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref(v___x_394_);
v_code_375_ = v_k_386_;
v_a_376_ = v___y_387_;
v_a_377_ = v___y_388_;
v_a_378_ = v___y_389_;
v_a_379_ = v___y_390_;
v_a_380_ = v___y_391_;
v_a_381_ = v___y_392_;
v_a_382_ = v___y_393_;
goto _start;
}
else
{
lean_dec_ref(v_k_386_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* v_funDecl_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_value_473_; lean_object* v___x_474_; 
v_value_473_ = lean_ctor_get(v_funDecl_464_, 4);
lean_inc_ref(v_value_473_);
lean_dec_ref(v_funDecl_464_);
v___x_474_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_value_473_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object* v_funDecl_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object* v_as_485_, lean_object* v_i_486_, lean_object* v_stop_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v_i_boxed_497_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_485_, v_i_boxed_497_, v_stop_boxed_498_, v_b_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_as_485_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object* v_code_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_509_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object* v_m_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_buckets_512_; lean_object* v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v_fold_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_buckets_512_ = lean_ctor_get(v_m_510_, 1);
v___x_513_ = lean_array_get_size(v_buckets_512_);
v___x_514_ = l_Lean_instHashableFVarId_hash(v_a_511_);
v___x_515_ = 32ULL;
v___x_516_ = lean_uint64_shift_right(v___x_514_, v___x_515_);
v_fold_517_ = lean_uint64_xor(v___x_514_, v___x_516_);
v___x_518_ = 16ULL;
v___x_519_ = lean_uint64_shift_right(v_fold_517_, v___x_518_);
v___x_520_ = lean_uint64_xor(v_fold_517_, v___x_519_);
v___x_521_ = lean_uint64_to_usize(v___x_520_);
v___x_522_ = lean_usize_of_nat(v___x_513_);
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_sub(v___x_522_, v___x_523_);
v___x_525_ = lean_usize_land(v___x_521_, v___x_524_);
v___x_526_ = lean_array_uget_borrowed(v_buckets_512_, v___x_525_);
v___x_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_511_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_m_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object* v_fvarId_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_used_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = lean_st_ref_get(v_a_533_);
v_used_536_ = lean_ctor_get(v___x_535_, 1);
lean_inc_ref(v_used_536_);
lean_dec(v___x_535_);
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_used_536_, v_fvarId_532_);
lean_dec_ref(v_used_536_);
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object* v_fvarId_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec(v_fvarId_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* v_fvarId_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_544_, v_a_546_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* v_fvarId_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_fvarId_554_);
return v_res_563_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object* v_00_u03b2_564_, lean_object* v_m_565_, lean_object* v_a_566_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_565_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object* v_00_u03b2_568_, lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(v_00_u03b2_568_, v_m_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_m_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0(void){
_start:
{
uint8_t v___x_573_; lean_object* v___x_574_; 
v___x_573_ = 0;
v___x_574_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* v_decls_575_, lean_object* v_i_576_, lean_object* v_code_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_lt(v___x_586_, v_i_576_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v_i_576_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_code_577_);
return v___x_588_;
}
else
{
uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_decl_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_a_596_; uint8_t v___x_597_; 
v___x_589_ = 0;
v___x_590_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_sub(v_i_576_, v___x_591_);
lean_dec(v_i_576_);
v_decl_593_ = lean_array_get_borrowed(v___x_590_, v_decls_575_, v___x_592_);
v___x_594_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_593_);
v___x_595_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_594_, v_a_579_);
lean_dec(v___x_594_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_595_);
v___x_597_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_589_, v_decl_593_, v_a_582_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_dec_ref(v___x_598_);
v_i_576_ = v___x_592_;
goto _start;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___x_592_);
lean_dec_ref(v_code_577_);
v_a_600_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
switch(lean_obj_tag(v_decl_593_))
{
case 0:
{
lean_object* v_decl_608_; lean_object* v___x_609_; 
v_decl_608_ = lean_ctor_get(v_decl_593_, 0);
lean_inc_ref(v_decl_608_);
v___x_609_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_608_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v___x_609_);
lean_inc_ref(v_decl_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_decl_608_);
lean_ctor_set(v___x_610_, 1, v_code_577_);
v_i_576_ = v___x_592_;
v_code_577_ = v___x_610_;
goto _start;
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v___x_592_);
lean_dec_ref(v_code_577_);
v_a_612_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_609_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_609_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
case 1:
{
lean_object* v_decl_620_; lean_object* v___x_621_; 
v_decl_620_ = lean_ctor_get(v_decl_593_, 0);
lean_inc_ref(v_decl_620_);
v___x_621_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_620_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v___x_621_);
lean_inc_ref(v_decl_620_);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v_decl_620_);
lean_ctor_set(v___x_622_, 1, v_code_577_);
v_i_576_ = v___x_592_;
v_code_577_ = v___x_622_;
goto _start;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v___x_592_);
lean_dec_ref(v_code_577_);
v_a_624_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_621_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
default: 
{
lean_object* v_decl_632_; lean_object* v___x_633_; 
v_decl_632_ = lean_ctor_get(v_decl_593_, 0);
lean_inc_ref(v_decl_632_);
v___x_633_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_632_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v___x_633_);
lean_inc_ref(v_decl_632_);
v___x_634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_634_, 0, v_decl_632_);
lean_ctor_set(v___x_634_, 1, v_code_577_);
v_i_576_ = v___x_592_;
v_code_577_ = v___x_634_;
goto _start;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v___x_592_);
lean_dec_ref(v_code_577_);
v_a_636_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_633_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_633_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* v_decls_644_, lean_object* v_i_645_, lean_object* v_code_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_644_, v_i_645_, v_code_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_decls_644_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object* v_decl_656_, lean_object* v_h__1_657_, lean_object* v_h__2_658_, lean_object* v_h__3_659_){
_start:
{
switch(lean_obj_tag(v_decl_656_))
{
case 0:
{
lean_object* v_decl_660_; lean_object* v___x_661_; 
lean_dec(v_h__3_659_);
lean_dec(v_h__2_658_);
v_decl_660_ = lean_ctor_get(v_decl_656_, 0);
lean_inc_ref(v_decl_660_);
lean_dec_ref(v_decl_656_);
v___x_661_ = lean_apply_1(v_h__1_657_, v_decl_660_);
return v___x_661_;
}
case 1:
{
lean_object* v_decl_662_; lean_object* v___x_663_; 
lean_dec(v_h__3_659_);
lean_dec(v_h__1_657_);
v_decl_662_ = lean_ctor_get(v_decl_656_, 0);
lean_inc_ref(v_decl_662_);
lean_dec_ref(v_decl_656_);
v___x_663_ = lean_apply_1(v_h__2_658_, v_decl_662_);
return v___x_663_;
}
default: 
{
lean_object* v_decl_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_658_);
lean_dec(v_h__1_657_);
v_decl_664_ = lean_ctor_get(v_decl_656_, 0);
lean_inc_ref(v_decl_664_);
lean_dec_ref(v_decl_656_);
v___x_665_ = lean_apply_1(v_h__3_659_, v_decl_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object* v_motive_666_, lean_object* v_decl_667_, lean_object* v_h__1_668_, lean_object* v_h__2_669_, lean_object* v_h__3_670_){
_start:
{
switch(lean_obj_tag(v_decl_667_))
{
case 0:
{
lean_object* v_decl_671_; lean_object* v___x_672_; 
lean_dec(v_h__3_670_);
lean_dec(v_h__2_669_);
v_decl_671_ = lean_ctor_get(v_decl_667_, 0);
lean_inc_ref(v_decl_671_);
lean_dec_ref(v_decl_667_);
v___x_672_ = lean_apply_1(v_h__1_668_, v_decl_671_);
return v___x_672_;
}
case 1:
{
lean_object* v_decl_673_; lean_object* v___x_674_; 
lean_dec(v_h__3_670_);
lean_dec(v_h__1_668_);
v_decl_673_ = lean_ctor_get(v_decl_667_, 0);
lean_inc_ref(v_decl_673_);
lean_dec_ref(v_decl_667_);
v___x_674_ = lean_apply_1(v_h__2_669_, v_decl_673_);
return v___x_674_;
}
default: 
{
lean_object* v_decl_675_; lean_object* v___x_676_; 
lean_dec(v_h__2_669_);
lean_dec(v_h__1_668_);
v_decl_675_ = lean_ctor_get(v_decl_667_, 0);
lean_inc_ref(v_decl_675_);
lean_dec_ref(v_decl_667_);
v___x_676_ = lean_apply_1(v_h__3_670_, v_decl_675_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* v_decls_677_, lean_object* v_code_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_array_get_size(v_decls_677_);
v___x_688_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_677_, v___x_687_, v_code_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* v_decls_689_, lean_object* v_code_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_689_, v_code_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_decls_689_);
return v_res_699_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
}
#ifdef __cplusplus
}
#endif
