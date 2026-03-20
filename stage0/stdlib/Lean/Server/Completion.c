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
lean_object* v_snd_99_; lean_object* v_fst_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_171_; 
v_snd_99_ = lean_ctor_get(v_b_92_, 1);
v_fst_100_ = lean_ctor_get(v_b_92_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_b_92_);
if (v_isSharedCheck_171_ == 0)
{
v___x_102_ = v_b_92_;
v_isShared_103_ = v_isSharedCheck_171_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_100_);
lean_dec(v_b_92_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_171_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_size_104_; lean_object* v_buckets_105_; lean_object* v_a_106_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v_label_118_; lean_object* v_textEdit_x3f_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint64_t v___x_122_; uint64_t v___y_124_; 
v_size_104_ = lean_ctor_get(v_snd_99_, 0);
v_buckets_105_ = lean_ctor_get(v_snd_99_, 1);
v_a_106_ = lean_array_uget_borrowed(v_as_89_, v_i_91_);
v_label_118_ = lean_ctor_get(v_a_106_, 0);
v_textEdit_x3f_119_ = lean_ctor_get(v_a_106_, 4);
lean_inc(v_textEdit_x3f_119_);
lean_inc_ref(v_label_118_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_label_118_);
lean_ctor_set(v___x_120_, 1, v_textEdit_x3f_119_);
v___x_121_ = lean_array_get_size(v_buckets_105_);
v___x_122_ = lean_string_hash(v_label_118_);
if (lean_obj_tag(v_textEdit_x3f_119_) == 0)
{
uint64_t v___x_166_; 
v___x_166_ = 11ULL;
v___y_124_ = v___x_166_;
goto v___jp_123_;
}
else
{
lean_object* v_val_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; 
v_val_167_ = lean_ctor_get(v_textEdit_x3f_119_, 0);
v___x_168_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_167_);
v___x_169_ = 13ULL;
v___x_170_ = lean_uint64_mix_hash(v___x_168_, v___x_169_);
v___y_124_ = v___x_170_;
goto v___jp_123_;
}
v___jp_107_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_unbox(v_fst_108_);
lean_dec(v_fst_108_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_113_; 
lean_inc(v_a_106_);
v___x_111_ = lean_array_push(v_fst_100_, v_a_106_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_snd_109_);
lean_ctor_set(v___x_102_, 0, v___x_111_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
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
lean_object* v___x_116_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_snd_109_);
v___x_116_ = v___x_102_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_fst_100_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_snd_109_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v_a_94_ = v___x_116_;
goto v___jp_93_;
}
}
}
v___jp_123_:
{
uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v_fold_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v_bkt_137_; uint8_t v___x_138_; 
v___x_125_ = lean_uint64_mix_hash(v___x_122_, v___y_124_);
v___x_126_ = 32ULL;
v___x_127_ = lean_uint64_shift_right(v___x_125_, v___x_126_);
v_fold_128_ = lean_uint64_xor(v___x_125_, v___x_127_);
v___x_129_ = 16ULL;
v___x_130_ = lean_uint64_shift_right(v_fold_128_, v___x_129_);
v___x_131_ = lean_uint64_xor(v_fold_128_, v___x_130_);
v___x_132_ = lean_uint64_to_usize(v___x_131_);
v___x_133_ = lean_usize_of_nat(v___x_121_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_sub(v___x_133_, v___x_134_);
v___x_136_ = lean_usize_land(v___x_132_, v___x_135_);
v_bkt_137_ = lean_array_uget_borrowed(v_buckets_105_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_120_, v_bkt_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_162_; 
lean_inc_ref(v_buckets_105_);
lean_inc(v_size_104_);
v_isSharedCheck_162_ = !lean_is_exclusive(v_snd_99_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; 
v_unused_163_ = lean_ctor_get(v_snd_99_, 1);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_snd_99_, 0);
lean_dec(v_unused_164_);
v___x_140_ = v_snd_99_;
v_isShared_141_ = v_isSharedCheck_162_;
goto v_resetjp_139_;
}
else
{
lean_dec(v_snd_99_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_162_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_size_x27_144_; lean_object* v___x_145_; lean_object* v_buckets_x27_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_142_ = lean_box(0);
v___x_143_ = lean_unsigned_to_nat(1u);
v_size_x27_144_ = lean_nat_add(v_size_104_, v___x_143_);
lean_dec(v_size_104_);
lean_inc(v_bkt_137_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_120_);
lean_ctor_set(v___x_145_, 1, v___x_142_);
lean_ctor_set(v___x_145_, 2, v_bkt_137_);
v_buckets_x27_146_ = lean_array_uset(v_buckets_105_, v___x_136_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_nat_mul(v_size_x27_144_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(3u);
v___x_150_ = lean_nat_div(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_array_get_size(v_buckets_x27_146_);
v___x_152_ = lean_nat_dec_le(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v_val_153_; lean_object* v___x_155_; 
v_val_153_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_146_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_val_153_);
lean_ctor_set(v___x_140_, 0, v_size_x27_144_);
v___x_155_ = v___x_140_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_val_153_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(v___x_138_);
v_fst_108_ = v___x_156_;
v_snd_109_ = v___x_155_;
goto v___jp_107_;
}
}
else
{
lean_object* v___x_159_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_buckets_x27_146_);
lean_ctor_set(v___x_140_, 0, v_size_x27_144_);
v___x_159_ = v___x_140_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_buckets_x27_146_);
v___x_159_ = v_reuseFailAlloc_161_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(v___x_138_);
v_fst_108_ = v___x_160_;
v_snd_109_ = v___x_159_;
goto v___jp_107_;
}
}
}
}
else
{
lean_object* v___x_165_; 
lean_dec_ref(v___x_120_);
v___x_165_ = lean_box(v___x_138_);
v_fst_108_ = v___x_165_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_172_, lean_object* v_sz_173_, lean_object* v_i_174_, lean_object* v_b_175_){
_start:
{
size_t v_sz_boxed_176_; size_t v_i_boxed_177_; lean_object* v_res_178_; 
v_sz_boxed_176_ = lean_unbox_usize(v_sz_173_);
lean_dec(v_sz_173_);
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_res_178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_172_, v_sz_boxed_176_, v_i_boxed_177_, v_b_175_);
lean_dec_ref(v_as_172_);
return v_res_178_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = lean_unsigned_to_nat(16u);
v___x_183_ = lean_mk_array(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_index_186_; 
v___x_184_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_185_ = lean_unsigned_to_nat(0u);
v_index_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_index_186_, 0, v___x_185_);
lean_ctor_set(v_index_186_, 1, v___x_184_);
return v_index_186_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v_index_187_; lean_object* v_r_188_; lean_object* v___x_189_; 
v_index_187_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v_r_188_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_r_188_);
lean_ctor_set(v___x_189_, 1, v_index_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_190_){
_start:
{
lean_object* v___x_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v_fst_195_; 
v___x_191_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_sz_192_ = lean_array_size(v_items_190_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_190_, v_sz_192_, v___x_193_, v___x_191_);
v_fst_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_fst_195_);
lean_dec_ref(v___x_194_);
return v_fst_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_196_);
lean_dec_ref(v_items_196_);
return v_res_197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_202_, lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_202_, v_a_203_, v_x_204_);
lean_dec(v_x_204_);
lean_dec_ref(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_207_, lean_object* v_data_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_210_, lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_211_, v_source_212_, v_target_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_219_, lean_object* v_pos_220_, lean_object* v_caps_221_, lean_object* v_as_222_, size_t v_sz_223_, size_t v_i_224_, lean_object* v_b_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_a_229_; lean_object* v_completions_233_; uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_lt(v_i_224_, v_sz_223_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_b_225_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_a_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; 
v_a_241_ = lean_array_uget_borrowed(v_as_222_, v_i_224_);
v_fst_242_ = lean_ctor_get(v_a_241_, 0);
v_snd_243_ = lean_ctor_get(v_a_241_, 1);
v___x_244_ = l_Lean_Server_CancellableM_checkCancelled(v___y_226_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
if (lean_obj_tag(v_a_245_) == 0)
{
lean_object* v_a_246_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_246_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v_a_245_);
v_a_229_ = v_a_246_;
goto v___jp_228_;
}
else
{
lean_object* v_info_247_; 
lean_dec_ref(v_a_245_);
v_info_247_ = lean_ctor_get(v_fst_242_, 2);
switch(lean_obj_tag(v_info_247_))
{
case 1:
{
lean_object* v_hoverInfo_248_; lean_object* v_ctx_249_; lean_object* v_stx_250_; lean_object* v_id_251_; uint8_t v_danglingDot_252_; lean_object* v_lctx_253_; lean_object* v___x_254_; 
v_hoverInfo_248_ = lean_ctor_get(v_fst_242_, 0);
v_ctx_249_ = lean_ctor_get(v_fst_242_, 1);
v_stx_250_ = lean_ctor_get(v_info_247_, 0);
v_id_251_ = lean_ctor_get(v_info_247_, 1);
v_danglingDot_252_ = lean_ctor_get_uint8(v_info_247_, sizeof(void*)*4);
v_lctx_253_ = lean_ctor_get(v_info_247_, 2);
lean_inc_ref(v___y_226_);
lean_inc(v_hoverInfo_248_);
lean_inc(v_id_251_);
lean_inc(v_stx_250_);
lean_inc_ref(v_lctx_253_);
lean_inc_ref(v_ctx_249_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_254_ = l_Lean_Server_Completion_idCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_249_, v_lctx_253_, v_stx_250_, v_id_251_, v_hoverInfo_248_, v_danglingDot_252_, v___y_226_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v_a_255_) == 0)
{
lean_object* v_a_256_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_256_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v_a_255_);
v_a_229_ = v_a_256_;
goto v___jp_228_;
}
else
{
lean_object* v_a_257_; 
v_a_257_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_a_257_);
lean_dec_ref(v_a_255_);
v_completions_233_ = v_a_257_;
goto v___jp_232_;
}
}
else
{
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
return v___x_254_;
}
}
case 0:
{
lean_object* v_ctx_258_; lean_object* v_termInfo_259_; lean_object* v___x_260_; 
v_ctx_258_ = lean_ctor_get(v_fst_242_, 1);
v_termInfo_259_ = lean_ctor_get(v_info_247_, 0);
lean_inc_ref(v___y_226_);
lean_inc_ref(v_termInfo_259_);
lean_inc_ref(v_ctx_258_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_260_ = l_Lean_Server_Completion_dotCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_258_, v_termInfo_259_, v___y_226_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_260_);
if (lean_obj_tag(v_a_261_) == 0)
{
lean_object* v_a_262_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_262_ = lean_ctor_get(v_a_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v_a_261_);
v_a_229_ = v_a_262_;
goto v___jp_228_;
}
else
{
lean_object* v_a_263_; 
v_a_263_ = lean_ctor_get(v_a_261_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v_a_261_);
v_completions_233_ = v_a_263_;
goto v___jp_232_;
}
}
else
{
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
return v___x_260_;
}
}
case 2:
{
lean_object* v_ctx_264_; lean_object* v_id_265_; lean_object* v_lctx_266_; lean_object* v_expectedType_x3f_267_; lean_object* v___x_268_; 
v_ctx_264_ = lean_ctor_get(v_fst_242_, 1);
v_id_265_ = lean_ctor_get(v_info_247_, 1);
v_lctx_266_ = lean_ctor_get(v_info_247_, 2);
v_expectedType_x3f_267_ = lean_ctor_get(v_info_247_, 3);
lean_inc_ref(v___y_226_);
lean_inc(v_expectedType_x3f_267_);
lean_inc(v_id_265_);
lean_inc_ref(v_lctx_266_);
lean_inc_ref(v_ctx_264_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_268_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_264_, v_lctx_266_, v_id_265_, v_expectedType_x3f_267_, v___y_226_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v___x_268_);
if (lean_obj_tag(v_a_269_) == 0)
{
lean_object* v_a_270_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_270_ = lean_ctor_get(v_a_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref(v_a_269_);
v_a_229_ = v_a_270_;
goto v___jp_228_;
}
else
{
lean_object* v_a_271_; 
v_a_271_ = lean_ctor_get(v_a_269_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v_a_269_);
v_completions_233_ = v_a_271_;
goto v___jp_232_;
}
}
else
{
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
return v___x_268_;
}
}
case 3:
{
lean_object* v_ctx_272_; lean_object* v_id_273_; lean_object* v_lctx_274_; lean_object* v_structName_275_; lean_object* v___x_276_; 
v_ctx_272_ = lean_ctor_get(v_fst_242_, 1);
v_id_273_ = lean_ctor_get(v_info_247_, 1);
v_lctx_274_ = lean_ctor_get(v_info_247_, 2);
v_structName_275_ = lean_ctor_get(v_info_247_, 3);
lean_inc_ref(v___y_226_);
lean_inc(v_structName_275_);
lean_inc(v_id_273_);
lean_inc_ref(v_lctx_274_);
lean_inc_ref(v_ctx_272_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_276_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_272_, v_lctx_274_, v_id_273_, v_structName_275_, v___y_226_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
if (lean_obj_tag(v_a_277_) == 0)
{
lean_object* v_a_278_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_278_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref(v_a_277_);
v_a_229_ = v_a_278_;
goto v___jp_228_;
}
else
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_a_279_);
lean_dec_ref(v_a_277_);
v_completions_233_ = v_a_279_;
goto v___jp_232_;
}
}
else
{
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
return v___x_276_;
}
}
case 5:
{
lean_object* v_ctx_280_; lean_object* v_stx_281_; lean_object* v___x_282_; 
v_ctx_280_ = lean_ctor_get(v_fst_242_, 1);
v_stx_281_ = lean_ctor_get(v_info_247_, 0);
lean_inc_ref(v_caps_221_);
lean_inc(v_stx_281_);
lean_inc_ref(v_ctx_280_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_282_ = l_Lean_Server_Completion_optionCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_280_, v_stx_281_, v_caps_221_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
v_completions_233_ = v_a_283_;
goto v___jp_232_;
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_284_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
case 6:
{
lean_object* v_ctx_292_; lean_object* v_partialId_293_; lean_object* v___x_294_; 
v_ctx_292_ = lean_ctor_get(v_fst_242_, 1);
v_partialId_293_ = lean_ctor_get(v_info_247_, 1);
lean_inc_ref(v_caps_221_);
lean_inc(v_partialId_293_);
lean_inc_ref(v_ctx_292_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_294_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_292_, v_partialId_293_, v_caps_221_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v_completions_233_ = v_a_295_;
goto v___jp_232_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_296_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_304_; uint8_t v_danglingDot_305_; lean_object* v_scopeNames_306_; lean_object* v___x_307_; 
v_id_x3f_304_ = lean_ctor_get(v_info_247_, 1);
v_danglingDot_305_ = lean_ctor_get_uint8(v_info_247_, sizeof(void*)*3);
v_scopeNames_306_ = lean_ctor_get(v_info_247_, 2);
lean_inc(v_scopeNames_306_);
lean_inc(v_id_x3f_304_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_307_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_id_x3f_304_, v_danglingDot_305_, v_scopeNames_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v_completions_233_ = v_a_308_;
goto v___jp_232_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
case 8:
{
lean_object* v_ctx_317_; lean_object* v___x_318_; 
v_ctx_317_ = lean_ctor_get(v_fst_242_, 1);
lean_inc_ref(v_ctx_317_);
lean_inc(v_snd_243_);
lean_inc_ref(v_pos_220_);
lean_inc_ref(v_uri_219_);
v___x_318_ = l_Lean_Server_Completion_tacticCompletion(v_uri_219_, v_pos_220_, v_snd_243_, v_ctx_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v_completions_233_ = v_a_319_;
goto v___jp_232_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_320_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_318_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
default: 
{
lean_object* v_allCompletions_328_; 
v_allCompletions_328_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_completions_233_ = v_allCompletions_328_;
goto v___jp_232_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v___y_226_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_caps_221_);
lean_dec_ref(v_pos_220_);
lean_dec_ref(v_uri_219_);
v_a_329_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_244_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_244_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_a_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
v___jp_232_:
{
lean_object* v___x_234_; size_t v___x_235_; size_t v___x_236_; 
v___x_234_ = l_Array_append___redArg(v_b_225_, v_completions_233_);
lean_dec_ref(v_completions_233_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_224_, v___x_235_);
v_i_224_ = v___x_236_;
v_b_225_ = v___x_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_337_, lean_object* v_pos_338_, lean_object* v_caps_339_, lean_object* v_as_340_, lean_object* v_sz_341_, lean_object* v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
size_t v_sz_boxed_346_; size_t v_i_boxed_347_; lean_object* v_res_348_; 
v_sz_boxed_346_ = lean_unbox_usize(v_sz_341_);
lean_dec(v_sz_341_);
v_i_boxed_347_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_res_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_337_, v_pos_338_, v_caps_339_, v_as_340_, v_sz_boxed_346_, v_i_boxed_347_, v_b_343_, v___y_344_);
lean_dec_ref(v_as_340_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_349_, lean_object* v_pos_350_, lean_object* v_caps_351_, lean_object* v_as_352_, size_t v_sz_353_, size_t v_i_354_, lean_object* v_b_355_, lean_object* v___y_356_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_354_, v_sz_353_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v___y_356_);
lean_dec_ref(v_caps_351_);
lean_dec_ref(v_pos_350_);
lean_dec_ref(v_uri_349_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_b_355_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
else
{
lean_object* v_a_361_; size_t v_sz_362_; size_t v___x_363_; lean_object* v___x_364_; 
v_a_361_ = lean_array_uget_borrowed(v_as_352_, v_i_354_);
v_sz_362_ = lean_array_size(v_a_361_);
v___x_363_ = ((size_t)0ULL);
lean_inc_ref(v___y_356_);
lean_inc_ref(v_caps_351_);
lean_inc_ref(v_pos_350_);
lean_inc_ref(v_uri_349_);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_349_, v_pos_350_, v_caps_351_, v_a_361_, v_sz_362_, v___x_363_, v_b_355_, v___y_356_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
if (lean_obj_tag(v_a_365_) == 0)
{
lean_dec_ref(v_a_365_);
lean_dec_ref(v___y_356_);
lean_dec_ref(v_caps_351_);
lean_dec_ref(v_pos_350_);
lean_dec_ref(v_uri_349_);
return v___x_364_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_a_366_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref(v_a_365_);
v___x_367_ = lean_array_get_size(v_a_366_);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_nat_dec_eq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_a_366_);
lean_dec_ref(v___y_356_);
lean_dec_ref(v_caps_351_);
lean_dec_ref(v_pos_350_);
lean_dec_ref(v_uri_349_);
return v___x_364_;
}
else
{
size_t v___x_370_; size_t v___x_371_; 
lean_dec_ref(v___x_364_);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_354_, v___x_370_);
v_i_354_ = v___x_371_;
v_b_355_ = v_a_366_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___y_356_);
lean_dec_ref(v_caps_351_);
lean_dec_ref(v_pos_350_);
lean_dec_ref(v_uri_349_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_373_, lean_object* v_pos_374_, lean_object* v_caps_375_, lean_object* v_as_376_, lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_b_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_383_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_373_, v_pos_374_, v_caps_375_, v_as_376_, v_sz_boxed_382_, v_i_boxed_383_, v_b_379_, v___y_380_);
lean_dec_ref(v_as_376_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_385_, lean_object* v_pos_386_, lean_object* v_fileMap_387_, lean_object* v_hoverPos_388_, lean_object* v_cmdStx_389_, lean_object* v_infoTree_390_, lean_object* v_caps_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v_allCompletions_397_; size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_394_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_387_, v_hoverPos_388_, v_cmdStx_389_, v_infoTree_390_);
v_fst_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v___x_394_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v___x_394_);
v_allCompletions_397_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_398_ = lean_array_size(v_fst_395_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_385_, v_pos_386_, v_caps_391_, v_fst_395_, v_sz_398_, v___x_399_, v_allCompletions_397_, v_a_392_);
lean_dec(v_fst_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_434_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_434_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_434_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_434_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
if (lean_obj_tag(v_a_401_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_snd_396_);
v_a_405_ = lean_ctor_get(v_a_401_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_415_ == 0)
{
v___x_407_ = v_a_401_;
v_isShared_408_ = v_isSharedCheck_415_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v_a_401_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_415_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_410_);
v___x_412_ = v___x_403_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_433_; 
v_a_416_ = lean_ctor_get(v_a_401_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_433_ == 0)
{
v___x_418_ = v_a_401_;
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v_a_401_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; uint8_t v___y_422_; uint8_t v___x_430_; 
v___x_420_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_416_);
lean_dec(v_a_416_);
v___x_430_ = lean_unbox(v_snd_396_);
lean_dec(v_snd_396_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 1;
v___y_422_ = v___x_431_;
goto v___jp_421_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = 0;
v___y_422_ = v___x_432_;
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_423_, 0, v___x_420_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___y_422_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_425_ = v___x_418_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_425_);
v___x_427_ = v___x_403_;
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
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_snd_396_);
v_a_435_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_400_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_400_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* v_uri_443_, lean_object* v_pos_444_, lean_object* v_fileMap_445_, lean_object* v_hoverPos_446_, lean_object* v_cmdStx_447_, lean_object* v_infoTree_448_, lean_object* v_caps_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Server_Completion_find_x3f(v_uri_443_, v_pos_444_, v_fileMap_445_, v_hoverPos_446_, v_cmdStx_447_, v_infoTree_448_, v_caps_449_, v_a_450_);
return v_res_452_;
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
