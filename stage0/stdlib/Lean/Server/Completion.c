// Lean compiler output
// Module: Lean.Server.Completion
// Imports: public import Lean.Server.Completion.CompletionCollectors public import Std.Data.HashMap
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
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t l_Lean_Lsp_instHashableInsertReplaceEdit_hash(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqInsertReplaceEdit_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object*);
lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1;
static lean_once_cell_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2;
static lean_once_cell_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = l_Lean_Lsp_instBEqInsertReplaceEdit_beq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object* v_a_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
else
{
lean_object* v_key_16_; lean_object* v_tail_17_; uint8_t v___y_19_; lean_object* v_fst_21_; lean_object* v_snd_22_; lean_object* v_fst_23_; lean_object* v_snd_24_; uint8_t v___x_25_; 
v_key_16_ = lean_ctor_get(v_x_14_, 0);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v_fst_21_ = lean_ctor_get(v_key_16_, 0);
v_snd_22_ = lean_ctor_get(v_key_16_, 1);
v_fst_23_ = lean_ctor_get(v_a_13_, 0);
v_snd_24_ = lean_ctor_get(v_a_13_, 1);
v___x_25_ = lean_string_dec_eq(v_fst_21_, v_fst_23_);
if (v___x_25_ == 0)
{
v___y_19_ = v___x_25_;
goto v___jp_18_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_snd_22_, v_snd_24_);
v___y_19_ = v___x_26_;
goto v___jp_18_;
}
v___jp_18_:
{
if (v___y_19_ == 0)
{
v_x_14_ = v_tail_17_;
goto _start;
}
else
{
return v___y_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* v_a_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec_ref(v_a_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
return v_x_31_;
}
else
{
lean_object* v_key_33_; lean_object* v_value_34_; lean_object* v_tail_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_68_; 
v_key_33_ = lean_ctor_get(v_x_32_, 0);
v_value_34_ = lean_ctor_get(v_x_32_, 1);
v_tail_35_ = lean_ctor_get(v_x_32_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_68_ == 0)
{
v___x_37_ = v_x_32_;
v_isShared_38_ = v_isSharedCheck_68_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_tail_35_);
lean_inc(v_value_34_);
lean_inc(v_key_33_);
lean_dec(v_x_32_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_68_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; uint64_t v___x_42_; uint64_t v___y_44_; 
v_fst_39_ = lean_ctor_get(v_key_33_, 0);
v_snd_40_ = lean_ctor_get(v_key_33_, 1);
v___x_41_ = lean_array_get_size(v_x_31_);
v___x_42_ = lean_string_hash(v_fst_39_);
if (lean_obj_tag(v_snd_40_) == 0)
{
uint64_t v___x_63_; 
v___x_63_ = 11ULL;
v___y_44_ = v___x_63_;
goto v___jp_43_;
}
else
{
lean_object* v_val_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; 
v_val_64_ = lean_ctor_get(v_snd_40_, 0);
v___x_65_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_64_);
v___x_66_ = 13ULL;
v___x_67_ = lean_uint64_mix_hash(v___x_65_, v___x_66_);
v___y_44_ = v___x_67_;
goto v___jp_43_;
}
v___jp_43_:
{
uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v_fold_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_45_ = lean_uint64_mix_hash(v___x_42_, v___y_44_);
v___x_46_ = 32ULL;
v___x_47_ = lean_uint64_shift_right(v___x_45_, v___x_46_);
v_fold_48_ = lean_uint64_xor(v___x_45_, v___x_47_);
v___x_49_ = 16ULL;
v___x_50_ = lean_uint64_shift_right(v_fold_48_, v___x_49_);
v___x_51_ = lean_uint64_xor(v_fold_48_, v___x_50_);
v___x_52_ = lean_uint64_to_usize(v___x_51_);
v___x_53_ = lean_usize_of_nat(v___x_41_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_sub(v___x_53_, v___x_54_);
v___x_56_ = lean_usize_land(v___x_52_, v___x_55_);
v___x_57_ = lean_array_uget_borrowed(v_x_31_, v___x_56_);
lean_inc(v___x_57_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 2, v___x_57_);
v___x_59_ = v___x_37_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_key_33_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_value_34_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v___x_57_);
v___x_59_ = v_reuseFailAlloc_62_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; 
v___x_60_ = lean_array_uset(v_x_31_, v___x_56_, v___x_59_);
v_x_31_ = v___x_60_;
v_x_32_ = v_tail_35_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* v_i_69_, lean_object* v_source_70_, lean_object* v_target_71_){
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
v_target_77_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_target_71_, v_es_74_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* v_data_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_nbuckets_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_82_ = lean_array_get_size(v_data_81_);
v___x_83_ = lean_unsigned_to_nat(2u);
v_nbuckets_84_ = lean_nat_mul(v___x_82_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_box(0);
v___x_87_ = lean_mk_array(v_nbuckets_84_, v___x_86_);
v___x_88_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_85_, v_data_81_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object* v_as_89_, size_t v_sz_90_, size_t v_i_91_, lean_object* v_b_92_){
_start:
{
lean_object* v_a_94_; uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_lt(v_i_91_, v_sz_90_);
if (v___x_98_ == 0)
{
return v_b_92_;
}
else
{
lean_object* v_snd_99_; lean_object* v_fst_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_172_; 
v_snd_99_ = lean_ctor_get(v_b_92_, 1);
v_fst_100_ = lean_ctor_get(v_b_92_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_b_92_);
if (v_isSharedCheck_172_ == 0)
{
v___x_102_ = v_b_92_;
v_isShared_103_ = v_isSharedCheck_172_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_100_);
lean_dec(v_b_92_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_172_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_size_104_; lean_object* v_buckets_105_; lean_object* v_a_106_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v_label_119_; lean_object* v_textEdit_x3f_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint64_t v___x_123_; uint64_t v___y_125_; 
v_size_104_ = lean_ctor_get(v_snd_99_, 0);
v_buckets_105_ = lean_ctor_get(v_snd_99_, 1);
v_a_106_ = lean_array_uget_borrowed(v_as_89_, v_i_91_);
v_label_119_ = lean_ctor_get(v_a_106_, 0);
v_textEdit_x3f_120_ = lean_ctor_get(v_a_106_, 4);
lean_inc(v_textEdit_x3f_120_);
lean_inc_ref(v_label_119_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_label_119_);
lean_ctor_set(v___x_121_, 1, v_textEdit_x3f_120_);
v___x_122_ = lean_array_get_size(v_buckets_105_);
v___x_123_ = lean_string_hash(v_label_119_);
if (lean_obj_tag(v_textEdit_x3f_120_) == 0)
{
uint64_t v___x_167_; 
v___x_167_ = 11ULL;
v___y_125_ = v___x_167_;
goto v___jp_124_;
}
else
{
lean_object* v_val_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; 
v_val_168_ = lean_ctor_get(v_textEdit_x3f_120_, 0);
v___x_169_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_168_);
v___x_170_ = 13ULL;
v___x_171_ = lean_uint64_mix_hash(v___x_169_, v___x_170_);
v___y_125_ = v___x_171_;
goto v___jp_124_;
}
v___jp_107_:
{
uint8_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unbox(v_fst_108_);
lean_dec(v_fst_108_);
v___x_111_ = lean_bool_not(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_113_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_snd_109_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_fst_100_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_snd_109_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
v_a_94_ = v___x_113_;
goto v___jp_93_;
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc(v_a_106_);
v___x_115_ = lean_array_push(v_fst_100_, v_a_106_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_snd_109_);
lean_ctor_set(v___x_102_, 0, v___x_115_);
v___x_117_ = v___x_102_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_snd_109_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
v_a_94_ = v___x_117_;
goto v___jp_93_;
}
}
}
v___jp_124_:
{
uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_bkt_138_; uint8_t v___x_139_; 
v___x_126_ = lean_uint64_mix_hash(v___x_123_, v___y_125_);
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___x_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___x_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_122_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v_bkt_138_ = lean_array_uget_borrowed(v_buckets_105_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_121_, v_bkt_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_163_; 
lean_inc_ref(v_buckets_105_);
lean_inc(v_size_104_);
v_isSharedCheck_163_ = !lean_is_exclusive(v_snd_99_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_164_ = lean_ctor_get(v_snd_99_, 1);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_snd_99_, 0);
lean_dec(v_unused_165_);
v___x_141_ = v_snd_99_;
v_isShared_142_ = v_isSharedCheck_163_;
goto v_resetjp_140_;
}
else
{
lean_dec(v_snd_99_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_163_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_size_x27_145_; lean_object* v___x_146_; lean_object* v_buckets_x27_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_unsigned_to_nat(1u);
v_size_x27_145_ = lean_nat_add(v_size_104_, v___x_144_);
lean_dec(v_size_104_);
lean_inc(v_bkt_138_);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v___x_121_);
lean_ctor_set(v___x_146_, 1, v___x_143_);
lean_ctor_set(v___x_146_, 2, v_bkt_138_);
v_buckets_x27_147_ = lean_array_uset(v_buckets_105_, v___x_137_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_mul(v_size_x27_145_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(3u);
v___x_151_ = lean_nat_div(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_array_get_size(v_buckets_x27_147_);
v___x_153_ = lean_nat_dec_le(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v_val_154_; lean_object* v___x_156_; 
v_val_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_147_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_val_154_);
lean_ctor_set(v___x_141_, 0, v_size_x27_145_);
v___x_156_ = v___x_141_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_val_154_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_box(v___x_139_);
v_fst_108_ = v___x_157_;
v_snd_109_ = v___x_156_;
goto v___jp_107_;
}
}
else
{
lean_object* v___x_160_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_buckets_x27_147_);
lean_ctor_set(v___x_141_, 0, v_size_x27_145_);
v___x_160_ = v___x_141_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_buckets_x27_147_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(v___x_139_);
v_fst_108_ = v___x_161_;
v_snd_109_ = v___x_160_;
goto v___jp_107_;
}
}
}
}
else
{
lean_object* v___x_166_; 
lean_dec_ref_known(v___x_121_, 2);
v___x_166_ = lean_box(v___x_139_);
v_fst_108_ = v___x_166_;
v_snd_109_ = v_snd_99_;
goto v___jp_107_;
}
}
}
}
v___jp_93_:
{
size_t v___x_95_; size_t v___x_96_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_91_, v___x_95_);
v_i_91_ = v___x_96_;
v_b_92_ = v_a_94_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_173_, lean_object* v_sz_174_, lean_object* v_i_175_, lean_object* v_b_176_){
_start:
{
size_t v_sz_boxed_177_; size_t v_i_boxed_178_; lean_object* v_res_179_; 
v_sz_boxed_177_ = lean_unbox_usize(v_sz_174_);
lean_dec(v_sz_174_);
v_i_boxed_178_ = lean_unbox_usize(v_i_175_);
lean_dec(v_i_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_173_, v_sz_boxed_177_, v_i_boxed_178_, v_b_176_);
lean_dec_ref(v_as_173_);
return v_res_179_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_box(0);
v___x_183_ = lean_unsigned_to_nat(16u);
v___x_184_ = lean_mk_array(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_index_187_; 
v___x_185_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_186_ = lean_unsigned_to_nat(0u);
v_index_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_index_187_, 0, v___x_186_);
lean_ctor_set(v_index_187_, 1, v___x_185_);
return v_index_187_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v_index_188_; lean_object* v_r_189_; lean_object* v___x_190_; 
v_index_188_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v_r_189_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_r_189_);
lean_ctor_set(v___x_190_, 1, v_index_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_191_){
_start:
{
lean_object* v___x_192_; size_t v_sz_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v_fst_196_; 
v___x_192_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_sz_193_ = lean_array_size(v_items_191_);
v___x_194_ = ((size_t)0ULL);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_191_, v_sz_193_, v___x_194_, v___x_192_);
v_fst_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_fst_196_);
lean_dec_ref(v___x_195_);
return v_fst_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_197_);
lean_dec_ref(v_items_197_);
return v_res_198_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_199_, lean_object* v_a_200_, lean_object* v_x_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_200_, v_x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_203_, lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_203_, v_a_204_, v_x_205_);
lean_dec(v_x_205_);
lean_dec_ref(v_a_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_208_, lean_object* v_data_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_211_, lean_object* v_i_212_, lean_object* v_source_213_, lean_object* v_target_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_212_, v_source_213_, v_target_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_217_, v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_220_, lean_object* v_pos_221_, lean_object* v_caps_222_, lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_b_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_a_230_; lean_object* v_completions_234_; uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_b_226_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_a_242_; lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_245_; 
v_a_242_ = lean_array_uget_borrowed(v_as_223_, v_i_225_);
v_fst_243_ = lean_ctor_get(v_a_242_, 0);
v_snd_244_ = lean_ctor_get(v_a_242_, 1);
v___x_245_ = l_Lean_Server_CancellableM_checkCancelled(v___y_227_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
if (lean_obj_tag(v_a_246_) == 0)
{
lean_object* v_a_247_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_247_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v_a_246_, 1);
v_a_230_ = v_a_247_;
goto v___jp_229_;
}
else
{
lean_object* v_info_248_; 
lean_dec_ref_known(v_a_246_, 1);
v_info_248_ = lean_ctor_get(v_fst_243_, 2);
switch(lean_obj_tag(v_info_248_))
{
case 1:
{
lean_object* v_hoverInfo_249_; lean_object* v_ctx_250_; lean_object* v_stx_251_; lean_object* v_id_252_; uint8_t v_danglingDot_253_; lean_object* v_lctx_254_; lean_object* v___x_255_; 
v_hoverInfo_249_ = lean_ctor_get(v_fst_243_, 0);
v_ctx_250_ = lean_ctor_get(v_fst_243_, 1);
v_stx_251_ = lean_ctor_get(v_info_248_, 0);
v_id_252_ = lean_ctor_get(v_info_248_, 1);
v_danglingDot_253_ = lean_ctor_get_uint8(v_info_248_, sizeof(void*)*4);
v_lctx_254_ = lean_ctor_get(v_info_248_, 2);
lean_inc(v_hoverInfo_249_);
lean_inc(v_id_252_);
lean_inc(v_stx_251_);
lean_inc_ref(v_lctx_254_);
lean_inc_ref(v_ctx_250_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_255_ = l_Lean_Server_Completion_idCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_250_, v_lctx_254_, v_stx_251_, v_id_252_, v_hoverInfo_249_, v_danglingDot_253_, v___y_227_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
if (lean_obj_tag(v_a_256_) == 0)
{
lean_object* v_a_257_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_257_ = lean_ctor_get(v_a_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v_a_256_, 1);
v_a_230_ = v_a_257_;
goto v___jp_229_;
}
else
{
lean_object* v_a_258_; 
v_a_258_ = lean_ctor_get(v_a_256_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v_a_256_, 1);
v_completions_234_ = v_a_258_;
goto v___jp_233_;
}
}
else
{
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
return v___x_255_;
}
}
case 0:
{
lean_object* v_ctx_259_; lean_object* v_termInfo_260_; lean_object* v___x_261_; 
v_ctx_259_ = lean_ctor_get(v_fst_243_, 1);
v_termInfo_260_ = lean_ctor_get(v_info_248_, 0);
lean_inc_ref(v_termInfo_260_);
lean_inc_ref(v_ctx_259_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_261_ = l_Lean_Server_Completion_dotCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_259_, v_termInfo_260_, v___y_227_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v_a_263_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_263_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_a_262_, 1);
v_a_230_ = v_a_263_;
goto v___jp_229_;
}
else
{
lean_object* v_a_264_; 
v_a_264_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v_a_262_, 1);
v_completions_234_ = v_a_264_;
goto v___jp_233_;
}
}
else
{
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
return v___x_261_;
}
}
case 2:
{
lean_object* v_ctx_265_; lean_object* v_id_266_; lean_object* v_lctx_267_; lean_object* v_expectedType_x3f_268_; lean_object* v___x_269_; 
v_ctx_265_ = lean_ctor_get(v_fst_243_, 1);
v_id_266_ = lean_ctor_get(v_info_248_, 1);
v_lctx_267_ = lean_ctor_get(v_info_248_, 2);
v_expectedType_x3f_268_ = lean_ctor_get(v_info_248_, 3);
lean_inc(v_expectedType_x3f_268_);
lean_inc(v_id_266_);
lean_inc_ref(v_lctx_267_);
lean_inc_ref(v_ctx_265_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_269_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_265_, v_lctx_267_, v_id_266_, v_expectedType_x3f_268_, v___y_227_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
if (lean_obj_tag(v_a_270_) == 0)
{
lean_object* v_a_271_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_271_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v_a_270_, 1);
v_a_230_ = v_a_271_;
goto v___jp_229_;
}
else
{
lean_object* v_a_272_; 
v_a_272_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v_a_270_, 1);
v_completions_234_ = v_a_272_;
goto v___jp_233_;
}
}
else
{
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
return v___x_269_;
}
}
case 3:
{
lean_object* v_ctx_273_; lean_object* v_id_274_; lean_object* v_lctx_275_; lean_object* v_structName_276_; lean_object* v___x_277_; 
v_ctx_273_ = lean_ctor_get(v_fst_243_, 1);
v_id_274_ = lean_ctor_get(v_info_248_, 1);
v_lctx_275_ = lean_ctor_get(v_info_248_, 2);
v_structName_276_ = lean_ctor_get(v_info_248_, 3);
lean_inc(v_structName_276_);
lean_inc(v_id_274_);
lean_inc_ref(v_lctx_275_);
lean_inc_ref(v_ctx_273_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_277_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_273_, v_lctx_275_, v_id_274_, v_structName_276_, v___y_227_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
if (lean_obj_tag(v_a_278_) == 0)
{
lean_object* v_a_279_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_279_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v_a_278_, 1);
v_a_230_ = v_a_279_;
goto v___jp_229_;
}
else
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v_a_278_, 1);
v_completions_234_ = v_a_280_;
goto v___jp_233_;
}
}
else
{
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
return v___x_277_;
}
}
case 5:
{
lean_object* v_ctx_281_; lean_object* v_stx_282_; lean_object* v___x_283_; 
v_ctx_281_ = lean_ctor_get(v_fst_243_, 1);
v_stx_282_ = lean_ctor_get(v_info_248_, 0);
lean_inc_ref(v_caps_222_);
lean_inc(v_stx_282_);
lean_inc_ref(v_ctx_281_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_283_ = l_Lean_Server_Completion_optionCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_281_, v_stx_282_, v_caps_222_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v_completions_234_ = v_a_284_;
goto v___jp_233_;
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_285_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_283_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
case 6:
{
lean_object* v_ctx_293_; lean_object* v_partialId_294_; lean_object* v___x_295_; 
v_ctx_293_ = lean_ctor_get(v_fst_243_, 1);
v_partialId_294_ = lean_ctor_get(v_info_248_, 1);
lean_inc_ref(v_caps_222_);
lean_inc(v_partialId_294_);
lean_inc_ref(v_ctx_293_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_295_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_293_, v_partialId_294_, v_caps_222_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v_completions_234_ = v_a_296_;
goto v___jp_233_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_297_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_295_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_305_; uint8_t v_danglingDot_306_; lean_object* v_scopeNames_307_; lean_object* v___x_308_; 
v_id_x3f_305_ = lean_ctor_get(v_info_248_, 1);
v_danglingDot_306_ = lean_ctor_get_uint8(v_info_248_, sizeof(void*)*3);
v_scopeNames_307_ = lean_ctor_get(v_info_248_, 2);
lean_inc(v_scopeNames_307_);
lean_inc(v_id_x3f_305_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_308_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_id_x3f_305_, v_danglingDot_306_, v_scopeNames_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v_completions_234_ = v_a_309_;
goto v___jp_233_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_310_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
case 8:
{
lean_object* v_ctx_318_; lean_object* v___x_319_; 
v_ctx_318_ = lean_ctor_get(v_fst_243_, 1);
lean_inc_ref(v_ctx_318_);
lean_inc(v_snd_244_);
lean_inc_ref(v_pos_221_);
lean_inc_ref(v_uri_220_);
v___x_319_ = l_Lean_Server_Completion_tacticCompletion(v_uri_220_, v_pos_221_, v_snd_244_, v_ctx_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v_completions_234_ = v_a_320_;
goto v___jp_233_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_321_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_319_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
default: 
{
lean_object* v_allCompletions_329_; 
v_allCompletions_329_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_completions_234_ = v_allCompletions_329_;
goto v___jp_233_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_b_226_);
lean_dec_ref(v_caps_222_);
lean_dec_ref(v_pos_221_);
lean_dec_ref(v_uri_220_);
v_a_330_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_245_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_245_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_a_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
v___jp_233_:
{
lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v___x_235_ = l_Array_append___redArg(v_b_226_, v_completions_234_);
lean_dec_ref(v_completions_234_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_225_, v___x_236_);
v_i_225_ = v___x_237_;
v_b_226_ = v___x_235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_338_, lean_object* v_pos_339_, lean_object* v_caps_340_, lean_object* v_as_341_, lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_348_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_338_, v_pos_339_, v_caps_340_, v_as_341_, v_sz_boxed_347_, v_i_boxed_348_, v_b_344_, v___y_345_);
lean_dec_ref(v___y_345_);
lean_dec_ref(v_as_341_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_350_, lean_object* v_pos_351_, lean_object* v_caps_352_, lean_object* v_as_353_, size_t v_sz_354_, size_t v_i_355_, lean_object* v_b_356_, lean_object* v___y_357_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_lt(v_i_355_, v_sz_354_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_caps_352_);
lean_dec_ref(v_pos_351_);
lean_dec_ref(v_uri_350_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_b_356_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v_a_362_; size_t v_sz_363_; size_t v___x_364_; lean_object* v___x_365_; 
v_a_362_ = lean_array_uget_borrowed(v_as_353_, v_i_355_);
v_sz_363_ = lean_array_size(v_a_362_);
v___x_364_ = ((size_t)0ULL);
lean_inc_ref(v_caps_352_);
lean_inc_ref(v_pos_351_);
lean_inc_ref(v_uri_350_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_350_, v_pos_351_, v_caps_352_, v_a_362_, v_sz_363_, v___x_364_, v_b_356_, v___y_357_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
if (lean_obj_tag(v_a_366_) == 0)
{
lean_dec_ref_known(v_a_366_, 1);
lean_dec_ref(v_caps_352_);
lean_dec_ref(v_pos_351_);
lean_dec_ref(v_uri_350_);
return v___x_365_;
}
else
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
v_a_367_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v_a_366_, 1);
v___x_368_ = lean_array_get_size(v_a_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
v___x_371_ = lean_bool_not(v___x_370_);
if (v___x_371_ == 0)
{
size_t v___x_372_; size_t v___x_373_; 
lean_dec_ref_known(v___x_365_, 1);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_355_, v___x_372_);
v_i_355_ = v___x_373_;
v_b_356_ = v_a_367_;
goto _start;
}
else
{
lean_dec(v_a_367_);
lean_dec_ref(v_caps_352_);
lean_dec_ref(v_pos_351_);
lean_dec_ref(v_uri_350_);
return v___x_365_;
}
}
}
else
{
lean_dec_ref(v_caps_352_);
lean_dec_ref(v_pos_351_);
lean_dec_ref(v_uri_350_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_375_, lean_object* v_pos_376_, lean_object* v_caps_377_, lean_object* v_as_378_, lean_object* v_sz_379_, lean_object* v_i_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_379_);
lean_dec(v_sz_379_);
v_i_boxed_385_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_375_, v_pos_376_, v_caps_377_, v_as_378_, v_sz_boxed_384_, v_i_boxed_385_, v_b_381_, v___y_382_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v_as_378_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_387_, lean_object* v_pos_388_, lean_object* v_fileMap_389_, lean_object* v_hoverPos_390_, lean_object* v_cmdStx_391_, lean_object* v_infoTree_392_, lean_object* v_caps_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_fst_397_; lean_object* v_snd_398_; lean_object* v_allCompletions_399_; size_t v_sz_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_396_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_389_, v_hoverPos_390_, v_cmdStx_391_, v_infoTree_392_);
v_fst_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_fst_397_);
v_snd_398_ = lean_ctor_get(v___x_396_, 1);
lean_inc(v_snd_398_);
lean_dec_ref(v___x_396_);
v_allCompletions_399_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_400_ = lean_array_size(v_fst_397_);
v___x_401_ = ((size_t)0ULL);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_387_, v_pos_388_, v_caps_393_, v_fst_397_, v_sz_400_, v___x_401_, v_allCompletions_399_, v_a_394_);
lean_dec(v_fst_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_433_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_433_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_433_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_433_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
if (lean_obj_tag(v_a_403_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_snd_398_);
v_a_407_ = lean_ctor_get(v_a_403_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_417_ == 0)
{
v___x_409_ = v_a_403_;
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v_a_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_412_);
v___x_414_ = v___x_405_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_432_; 
v_a_418_ = lean_ctor_get(v_a_403_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_432_ == 0)
{
v___x_420_ = v_a_403_;
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_a_403_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; uint8_t v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_422_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_418_);
lean_dec(v_a_418_);
v___x_423_ = lean_unbox(v_snd_398_);
lean_dec(v_snd_398_);
v___x_424_ = lean_bool_not(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_425_);
v___x_427_ = v___x_420_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_427_);
v___x_429_ = v___x_405_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_snd_398_);
v_a_434_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_402_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_402_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* v_uri_442_, lean_object* v_pos_443_, lean_object* v_fileMap_444_, lean_object* v_hoverPos_445_, lean_object* v_cmdStx_446_, lean_object* v_infoTree_447_, lean_object* v_caps_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Server_Completion_find_x3f(v_uri_442_, v_pos_443_, v_fileMap_444_, v_hoverPos_445_, v_cmdStx_446_, v_infoTree_447_, v_caps_448_, v_a_449_);
lean_dec_ref(v_a_449_);
return v_res_451_;
}
}
lean_object* runtime_initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Completion_CompletionCollectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionCollectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion(builtin);
}
#ifdef __cplusplus
}
#endif
